<#
.SYNOPSIS
    Paper <-> Lean consistency check.  Run after EVERY step of development.

.DESCRIPTION
    The paper has no LaTeX labels, only numbers, so a declaration that formalizes
    a numbered item of the paper opens its docstring with that item's number,
    written as

        /-- `#theorem 2#` (§IV): r_f(k,t_d,t_f) = N(D_f(t_d,t_f : u_1,...,u_{q^k})). -/
        theorem optimalRedundancyData_eq_N_drmData : ... := by sorry

    (the full table: `#definition N#`, `#theorem N#`, `#lemma N#`,
    `#corollary N#`, `#example N#`, `#remark N#`; see Notation.md section 1).
    Helpers that are not a paper item open their docstring with `(internal)` or
    `(paper notation, ...)` instead.

    This script checks:
    1. the project builds (incremental);
    2. every marker used in FCC/*.lean is a row of the inventory in PLAN.md
       (Lean -> plan: no invented labels);
    3. every inventory row that carries a Lean name is *stated*: the declaration
       named in the row's "Lean name" column exists, and the docstring directly
       above it opens with the row's marker (plan -> Lean).  Without -Strict a
       missing row is a warning (the catalogue is filled in during phase 2);
       with -Strict it is a failure, which is the milestone M2 gate;
    4. every module under FCC/ is imported by the library root module (no orphan
       modules that `lake build` would silently skip);
    5. how many `sorry` statements remain (the authoritative stub gate is
       scripts/axioms_check.ps1, which fails on `sorryAx`).

    These checks are label-level only.  The paper ships as a PDF, so the semantic
    comparison of the paper's statements with the inventory table cannot be
    automated: that is the manual checklist in CONSISTENCY.md.

.PARAMETER Strict
    Fail when an inventory row with a Lean name has no matching declaration.

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

# A paper marker such as `#theorem 2#`; the key normalises away the whitespace.
$markerPattern = '#(definition|theorem|lemma|corollary|example|remark)\s*([0-9]+)#'
$declPattern = '^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*(?:def|theorem|lemma|abbrev|instance|structure|class|inductive)\s+'
$planPath = 'PLAN.md'

function Get-MarkerKeys([string]$text) {
  $keys = @()
  foreach ($m in [regex]::Matches($text, $markerPattern)) {
    $keys += ($m.Value -replace '\s+', '')
  }
  return $keys
}

function Get-DocstringWindow([string[]]$lines, [int]$declIndex) {
  $start = $declIndex
  for ($j = $declIndex - 1; $j -ge 0 -and ($declIndex - $j) -le 30; $j--) {
    if ($lines[$j] -match $declPattern) { break }
    if ($lines[$j] -match '^\s*(end|namespace|section|import|open|variable|set_option|attribute)\b') { break }
    $start = $j
  }
  return ($lines[$start..$declIndex] -join "`n")
}

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

# ------------------------------------- 2. inventory: rows, status, Lean names
if (-not (Test-Path $planPath)) {
  Write-Host "FAIL: missing $planPath"
  exit 1
}
$rows = @()
$knownKeys = @{}
foreach ($line in Get-Content $planPath) {
  if ($line -notmatch '^\s*\|') { continue }
  $cells = @($line -split '\|' | ForEach-Object { $_.Trim() })
  $allKeys = @()
  foreach ($c in $cells) { $allKeys += Get-MarkerKeys $c }
  if ($allKeys.Count -eq 0) { continue }
  foreach ($k in $allKeys) { $knownKeys[$k] = $true }

  # The row's own label is the marker in its FIRST non-empty cell (the "Label"
  # column); markers mentioned later in the row are only cross-references.
  $selfKeys = @()
  for ($i = 1; $i -lt $cells.Count; $i++) {
    if ($cells[$i] -eq '') { continue }
    $selfKeys = Get-MarkerKeys $cells[$i]
    break
  }
  if ($selfKeys.Count -eq 0) { continue }

  # The statement column may itself contain `|` (set-builder notation), so the
  # columns are located from the END of the row: last non-empty cell = status,
  # the one before it = "Lean name".
  $status = ''
  $nameCell = ''
  $seen = 0
  for ($i = $cells.Count - 1; $i -ge 1; $i--) {
    if ($cells[$i] -eq '') { continue }
    $seen++
    if ($seen -eq 1) { $status = $cells[$i]; continue }
    if ($seen -eq 2) { $nameCell = $cells[$i]; break }
  }

  # "Lean name" is the fourth column of the inventory tables; it may list
  # several declarations (`IsDCode`, `N`, ...).  A dash or a prose cell means
  # "no owning declaration" (external results, remarks).
  $names = @()
  foreach ($m in [regex]::Matches($nameCell, '`([A-Za-z][A-Za-z0-9_]*)`')) { $names += $m.Groups[1].Value }
  if ($names.Count -eq 0 -and $nameCell -match '^[A-Za-z][A-Za-z0-9_]*$') { $names += $nameCell }

  foreach ($k in $selfKeys) {
    $rows += [pscustomobject]@{
      Key       = $k
      Status    = $status
      Names     = $names
      External  = ($status -match 'external')
      DeclRegex = @($names | ForEach-Object { $declPattern + [regex]::Escape($_) + '\b' })
    }
  }
}
Write-Host "== [2/5] inventory: $($rows.Count) row(s) with a paper marker, $($knownKeys.Count) marker(s) known =="

# ------------------------------------- 3. Lean -> plan (markers used)
Write-Host '== [3/5] Lean -> plan: every marker used in FCC/ must be an inventory row =='
$usedKeys = @{}
foreach ($f in $leanFiles) {
  $text = Get-Content -LiteralPath $f.FullName -Raw
  foreach ($k in (Get-MarkerKeys $text)) {
    if (-not $usedKeys.ContainsKey($k)) { $usedKeys[$k] = $f.Name }
  }
}
$bad = 0
foreach ($k in ($usedKeys.Keys | Sort-Object)) {
  if (-not $knownKeys.ContainsKey($k)) {
    Write-Host "  NOT in ${planPath}: $k (used in $($usedKeys[$k]))"
    $bad = 1
  }
}
if ($bad -eq 1) { $failed = 1 }
elseif ($usedKeys.Count -eq 0) { Write-Host '  ok: no paper marker used yet' }
else { Write-Host "  ok: all $($usedKeys.Count) marker(s) used in FCC/ are inventory rows" }

# ------------------------------------- 4. plan -> Lean (rows must be stated)
Write-Host '== [4/5] plan -> Lean: each row must be stated by its Lean name =='
$stated = @{}
foreach ($f in $leanFiles) {
  $lines = @(Get-Content -LiteralPath $f.FullName)
  for ($i = 0; $i -lt $lines.Count; $i++) {
    foreach ($row in $rows) {
      if ($row.External -or $row.DeclRegex.Count -eq 0) { continue }
      foreach ($rx in $row.DeclRegex) {
        if ($lines[$i] -notmatch $rx) { continue }
        $window = Get-DocstringWindow $lines $i
        if ((Get-MarkerKeys $window) -contains $row.Key) {
          $stated[$row.Key] = "$($f.Name):$($i + 1)"
        }
      }
    }
  }
}
$missing = @()
$unchecked = @()
foreach ($row in $rows) {
  if ($row.External) { continue }
  if ($row.DeclRegex.Count -eq 0) { $unchecked += $row.Key; continue }
  if (-not $stated.ContainsKey($row.Key)) { $missing += $row.Key }
}
if ($missing.Count -eq 0) {
  Write-Host "  ok: every row with a Lean name is stated ($($stated.Count) row(s))"
} elseif ($Strict) {
  foreach ($k in ($missing | Sort-Object)) { Write-Host "  NOT stated: $k" }
  $failed = 1
} else {
  Write-Host "  warn: $($missing.Count) row(s) not stated yet (phase 1/2 work):"
  Write-Host "        $(($missing | Sort-Object) -join ', ')"
}
if ($unchecked.Count -gt 0) {
  Write-Host "  note: $($unchecked.Count) row(s) carry no Lean name and are not checked: $(($unchecked | Sort-Object) -join ', ')"
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
  Write-Host 'OK: plan and Lean are in sync (build, markers, module graph).'
} else {
  Write-Host 'FAIL: see items above; fix before committing (CONSISTENCY.md).'
}
exit $failed
