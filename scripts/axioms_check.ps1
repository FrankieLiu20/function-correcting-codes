<#
.SYNOPSIS
    Axiom audit: every headline result must depend only on the standard axioms.

.DESCRIPTION
    Allowed axioms: propext, Quot.sound, Classical.choice (Lean's standard
    trusted base).  `sorryAx` anywhere fails the audit, naming the offender.

    Coverage is enforced by scripts/headline_theorems.txt: the manifest must
    match the `#print axioms` declarations in FCC/AxiomCheck.lean
    exactly, in both directions, so a headline theorem cannot be added or
    dropped without an explicit, reviewed change.

.EXAMPLE
    powershell -ExecutionPolicy Bypass -File scripts\axioms_check.ps1

.NOTES
    Works in both Windows PowerShell 5.1 (`powershell`) and PowerShell 7
    (`pwsh`).  The file is pure ASCII on purpose.
#>
[CmdletBinding()]
param()

$ErrorActionPreference = 'Continue'
$root = Split-Path -Parent $PSScriptRoot
Set-Location $root

$manifest = 'scripts/headline_theorems.txt'
$checkFile = 'FCC/AxiomCheck.lean'
$allow = @('propext', 'Quot.sound', 'Classical.choice')

Write-Host '== [1/4] elaborating FCC/AxiomCheck.lean =='
$out = & lake env lean $checkFile 2>&1
if ($LASTEXITCODE -ne 0) {
  Write-Host "ERROR: 'lake env lean $checkFile' failed"
  $out | Select-Object -Last 40
  exit 1
}
Write-Host '  ok'

Write-Host '== [2/4] coverage: manifest <-> AxiomCheck.lean =='
if (-not (Test-Path $manifest)) { Write-Host "FAIL: missing manifest $manifest"; exit 1 }
$declared = @(Select-String -LiteralPath $checkFile -Pattern '#print axioms ([A-Za-z0-9_\.]+)' |
  ForEach-Object { $_.Matches[0].Groups[1].Value } | Sort-Object -Unique)
if ($declared.Count -eq 0) { Write-Host "FAIL: no '#print axioms' declarations in $checkFile"; exit 1 }
$manifestNames = @(Get-Content $manifest | Where-Object { $_ -notmatch '^\s*(#|$)' } |
  ForEach-Object { $_.Trim() } | Sort-Object -Unique)
if ($manifestNames.Count -eq 0) { Write-Host "FAIL: manifest $manifest is empty"; exit 1 }

$missing = @($manifestNames | Where-Object { $declared -notcontains $_ })
$extra = @($declared | Where-Object { $manifestNames -notcontains $_ })
if ($missing.Count -gt 0) {
  Write-Host "  FAIL: headline theorems in $manifest missing a #print axioms in $checkFile :"
  $missing | ForEach-Object { Write-Host "    $_" }
  exit 1
}
if ($extra.Count -gt 0) {
  Write-Host "  FAIL: #print axioms in $checkFile not listed in $manifest :"
  $extra | ForEach-Object { Write-Host "    $_" }
  Write-Host '  add them to the manifest if they are headline theorems, or remove the #print.'
  exit 1
}
Write-Host "  ok ($($declared.Count) headline theorem(s))"

Write-Host '== [3/4] parsing the axiom lists =='
$seen = @{}
foreach ($line in $out) {
  $s = [string]$line
  if ($s -match "^\s*'?([A-Za-z0-9_\.]+)'?\s+depends on axioms:\s*\[(.*)\]\s*$") {
    $seen[$Matches[1]] = $Matches[2]
  } elseif ($s -match "^\s*'?([A-Za-z0-9_\.]+)'?\s+does not depend on any axioms") {
    $seen[$Matches[1]] = ''
  }
}
if ($seen.Count -eq 0) {
  Write-Host '  FAIL: could not parse any axiom list out of the #print axioms output.'
  Write-Host '  Raw output was:'
  $out | Select-Object -Last 40
  exit 1
}

Write-Host '== [4/4] allowlist =='
$bad = 0
foreach ($name in ($seen.Keys | Sort-Object)) {
  $axioms = @($seen[$name] -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ -ne '' })
  foreach ($a in $axioms) {
    if ($allow -notcontains $a) {
      Write-Host "  FAIL: $name depends on disallowed axiom: $a"
      $bad = 1
    }
  }
}
if (($out | Out-String) -match 'sorryAx') {
  Write-Host '  FAIL: sorryAx appears in the audit output (an unfinished proof)'
  $bad = 1
}

if ($bad -ne 0) {
  Write-Host 'FAIL: axiom audit failed.'
  exit 1
}
Write-Host "OK: per-theorem axiom audit passed ($($seen.Count) theorem(s); allowlist + manifest coverage)."
exit 0
