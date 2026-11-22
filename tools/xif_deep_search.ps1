<#
.SYNOPSIS
  SHEAF/IUT repo-first deep search (§7.9/§7.10). Run BEFORE writing any Lean file.
.DESCRIPTION
  Searches the whole relevant repository for a regex query across:
    LeanFormal/, Iut/, tmp/local-cft-port/, tmp/sheaf/xif/paper/, tmp/archive_sorry_20261028/,
    tmp/sheaf/gap-exploration-20261030/, vendor/promachina/snapshots/ (Lean, source ref),
    papers/motizuki_corpus/text/ (paper text).
  Output: path:line: text (capped). Also prints a compact hit-count summary.
.EXAMPLE
  tools/xif_deep_search.ps1 -Query 'sourceHaarActualFamily|sourceHaarActualTheater'
  tools/xif_deep_search.ps1 -Query 'height_le_weighted_logDiff|genEll_transfer' -MaxHits 60
#>
param(
  [Parameter(Mandatory = $true)][string]$Query,
  [string]$Root = 'D:\lean',
  [int]$MaxHits = 120,
  [int]$PerFile = 3,
  [switch]$NoCorpus
)
$rg = Get-Command rg -ErrorAction SilentlyContinue
if (-not $rg) { Write-Output 'ERROR: rg (ripgrep) not found on PATH'; exit 1 }

$leanRoots = @('LeanFormal', 'Iut', 'tmp/local-cft-port', 'tmp/sheaf/xif/paper', 'tmp/archive_sorry_20261028', 'tmp/sheaf/gap-exploration-20261030', 'vendor/promachina/snapshots')
$textRoots = @('papers/motizuki_corpus/text')

$excl = @('-g', '!**/.lake/**', '-g', '!**/.git/**', '-g', '!**/node_modules/**')

$results = New-Object System.Collections.Generic.List[string]
$summary = New-Object System.Collections.Generic.List[string]

foreach ($r in $leanRoots) {
  $p = Join-Path $Root $r
  if (-not (Test-Path $p)) { continue }
  $out = & rg -n --no-heading --color never -m $PerFile -e $Query @excl -g '*.lean' $p 2>$null
  $n = @($out).Count
  if ($n -gt 0) {
    $summary.Add(("LEAN  {0,-45} hits={1}" -f $r, $n))
    foreach ($line in @($out)) { $results.Add($line) }
  }
}
if (-not $NoCorpus) {
  foreach ($r in $textRoots) {
    $p = Join-Path $Root $r
    if (-not (Test-Path $p)) { continue }
    $out = & rg -n --no-heading --color never -m $PerFile -e $Query @excl -g '*.txt' $p 2>$null
    $n = @($out).Count
    if ($n -gt 0) {
      $summary.Add(("TEXT  {0,-45} hits={1}" -f $r, $n))
      foreach ($line in @($out)) { $results.Add($line) }
    }
  }
}

Write-Output ("QUERY: " + $Query)
Write-Output "=== summary ==="
if ($summary.Count -eq 0) { Write-Output 'NO HITS - record "prior art: none" in coord/PRIOR-ART-INDEX.md' }
else { $summary | ForEach-Object { Write-Output $_ } }
Write-Output "=== hits (capped at $MaxHits) ==="
$results | Select-Object -First $MaxHits | ForEach-Object { $t = $_.ToString(); if ($t.Length -gt 240) { $t.Substring(0, 240) } else { $t } }
Write-Output ("total hit lines (pre-cap): " + $results.Count)
