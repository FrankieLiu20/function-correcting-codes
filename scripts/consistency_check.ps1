<#
.SYNOPSIS
    Paper <-> Lean consistency check.  Run after EVERY step of development.

.DESCRIPTION
    1. builds the project (incremental);
    2. checks that every paper label referenced from an FCC/*.lean docstring or
       comment exists in the inventory table of PLAN.md (Lean -> plan);
    3. checks that every catalogue row of the PLAN.md inventory is stated
       somewhere in the library (plan -> Lean).  Without -Strict a missing row
       is a warning (the catalogue is filled in during phase 2); with -Strict it
       is a failure, which is the milestone M2 gate (see PLAN.md section 6);
    4. checks that every module under FCC/ is imported by the library root
       module (no orphan modules that `lake build` would silently skip);
    5. reports how many `sorry` statements remain in code (comments and
       docstrings excluded; the authoritative stub gate is
       scripts/axioms_check.ps1, which fails on `sorryAx`).

    These checks are label-level only.  The paper is available only as a PDF
    (paper/*.pdf, git-ignored), so the semantic comparison of the paper's
    statements with the inventory table cannot be automated: it is the manual
    checklist in CONSISTENCY.md.

    Convention checked by [4/5]: the docstring of the declaration that owns a
    paper statement OPEN with the backticked label, i.e. the file contains a
    line

        /-- `thm:2` (Theorem 2, §IV): ...

    A label merely mentioned inside prose does not count as a stated result.

.PARAMETER Strict
    Fail when a catalogue row of PLAN.md has no declaration in the library.

.EXAMPLE
    powershell -ExecutionPolicy Bypass -File scripts\consistency_check.ps1
    powershell -ExecutionPolicy Bypass -File scripts\consistency_check.ps1 -Strict

.NOTES
    Works in both Windows PowerShell 5.1 (`powershell`) and PowerShell 7
    (`pwsh`).  The file is pure ASCII on purpose: Windows PowerShell 5.1 reads
    .ps1 files as ANSI unless they carry a byte-order mark.
#>
[CmdletBinding()]
param([switch]$Strict)

$ErrorActionPreference = 'Continue'
$root = Split-Path -Parent $PSScriptRoot
Set-Location $root
$failed = 0

$labelPattern = '(def|thm|lem|cor|ex|rem):[0-9]+'
$planPath = 'PLAN.md'

# ------------------------------------------------------------------- 1. build
Write-Host '== [1/5] lake build (incremental) =='
lake build
if ($LASTEXITCODE -ne 0) {
  Write-Host 'FAIL: build'
  exit 1
}

$leanFiles = @(Get-ChildItem 'FCC' -Filter *.lean -ErrorAction SilentlyContinue)
if ($leanFiles.Count -eq 0) {
  Write-Host 'FAIL: no Lean modules found under FCC/'
  exit 1
}

# ------------------------------------- 2. inventory: labels and row status
if (-not (Test-Path $planPath)) {
  Write-Host "FAIL: missing $planPath"
  exit 1
}
$planLabels = @{}
$catalogueStatus = @{}
foreach ($line in Get-Content $planPath) {
  if ($line -notmatch '^\s*\|') { continue }
  $cells = @($line -split '\|' | ForEach-Object { $_.Trim() })
  $rowLabels = @()
  foreach ($c in $cells) {
    foreach ($m in [regex]::Matches($c, "(?<![A-Za-z0-9_])$labelPattern")) {
      if ($rowLabels -notcontains $m.Value) { $rowLabels += $m.Value }
    }
  }
  if ($rowLabels.Count -eq 0) { continue }
  # The row's own label is the one in its FIRST non-empty cell (the "Label"
  # column); labels mentioned later in the row (e.g. "needs `thm:12`") are only
  # known labels, they must not inherit this row's status.
  $firstCell = ''
  for ($i = 1; $i -lt $cells.Count; $i++) {
    if ($cells[$i] -ne '') { $firstCell = $cells[$i]; break }
  }
  $status = ''
  for ($i = $cells.Count - 1; $i -ge 1; $i--) {
    if ($cells[$i] -ne '') { $status = $cells[$i]; break }
  }
  foreach ($lb in $rowLabels) {
    $planLabels[$lb] = $true
  }
  foreach ($m in [regex]::Matches($firstCell, "(?<![A-Za-z0-9_])$labelPattern")) {
    if ($status -match 'external') { $catalogueStatus[$m.Value] = 'external' }
    else { $catalogueStatus[$m.Value] = $status }
  }
}
Write-Host "== [2/5] inventory: $($planLabels.Count) label(s) listed in $planPath =="

# ------------------------------------- 3. Lean -> plan (labels used)
Write-Host '== [3/5] Lean -> plan: referenced labels must be in the inventory =='
$leanLabels = @{}
foreach ($f in $leanFiles) {
  $t = Get-Content -LiteralPath $f.FullName -Raw
  foreach ($m in [regex]::Matches($t, '`(def|thm|lem|cor|ex|rem):[0-9]+`')) {
    $leanLabels[$m.Value.Trim('`')] = $f.Name
  }
}
$bad = 0
foreach ($lb in ($leanLabels.Keys | Sort-Object)) {
  if (-not $planLabels.ContainsKey($lb)) {
    Write-Host "  NOT in ${planPath}: $lb (mentioned in $($leanLabels[$lb]))"
    $bad = 1
  }
}
if ($bad -eq 1) { $failed = 1 }
elseif ($leanLabels.Count -eq 0) { Write-Host '  ok: no paper label referenced yet' }
else { Write-Host "  ok: all $($leanLabels.Count) referenced label(s) are in the inventory" }

# ------------------------------------- 4. plan -> Lean (catalogue coverage)
Write-Host '== [4/5] plan -> Lean: catalogue rows must be stated in the library =='
$openPattern = '^/-{1,2}\s*`(def|thm|lem|cor|ex|rem):[0-9]+`'
$statedLabels = @{}
foreach ($f in $leanFiles) {
  foreach ($line in Get-Content -LiteralPath $f.FullName) {
    if ($line -match $openPattern) {
      $lb = [regex]::Match($line, '`(def|thm|lem|cor|ex|rem):[0-9]+`').Value.Trim('`')
      $statedLabels[$lb] = $f.Name
    }
  }
}
$missing = @()
foreach ($lb in ($catalogueStatus.Keys | Sort-Object)) {
  if ($catalogueStatus[$lb] -eq 'external') { continue }
  if (-not $statedLabels.ContainsKey($lb)) { $missing += $lb }
}
if ($missing.Count -eq 0) {
  Write-Host '  ok: every catalogue row is stated'
} elseif ($Strict) {
  foreach ($lb in $missing) { Write-Host "  NOT stated: $lb" }
  $failed = 1
} else {
  Write-Host "  warn: $($missing.Count) catalogue row(s) not stated yet (phase 2 work):"
  Write-Host "        $($missing -join ', ')"
}

# ------------------------------------------ 5. orphans, module graph, sorry
Write-Host '== [5/5] module graph and sorry count =='
$orphans = 0
foreach ($f in $leanFiles) {
  $importLine = "import FCC.$($f.BaseName)"
  $hit = $false
  foreach ($g in @(Get-ChildItem -Filter *.lean) + $leanFiles) {
    if ($g.FullName -eq $f.FullName) { continue }
    if (Select-String -LiteralPath $g.FullName -Pattern $importLine -SimpleMatch -Quiet) { $hit = $true; break }
  }
  if (-not $hit) {
    Write-Host "  NOT imported by any module: FCC/$($f.BaseName).lean"
    $orphans = 1
  }
}
if ($orphans -eq 1) { $failed = 1 } else { Write-Host '  ok: all FCC modules are imported' }

$sorryCount = 0
foreach ($f in $leanFiles) {
  foreach ($line in Get-Content -LiteralPath $f.FullName) {
    if ($line -match '^\s*(\u00B7\s*)?sorry(\s|$)') { $sorryCount++ }
  }
}
Write-Host "  sorry statements in code: $sorryCount (comments/docstrings excluded;"
Write-Host '                            see scripts/axioms_check.ps1 for the stub gate)'

if ($failed -eq 0) {
  Write-Host 'OK: plan and Lean are in sync (build, labels, module graph).'
} else {
  Write-Host 'FAIL: see items above; fix before committing (CONSISTENCY.md).'
}
exit $failed
