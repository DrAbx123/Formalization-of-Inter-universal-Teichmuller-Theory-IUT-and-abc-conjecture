<#
.SYNOPSIS
  Script-based autofix for ported external Lean files: apply rename dictionary to failed files,
  ensure olean dirs, requeue only files that were actually patched (dependency ordering is
  handled by xif_port_feeder.ps1).
#>
param(
  [string]$Root = 'D:\lean',
  [string]$Rules = 'D:\lean\tools\port_rename_map.txt',
  [int]$MaxFiles = 400,
  [switch]$DryRun
)
$ErrorActionPreference = 'Continue'
$results = Join-Path $Root 'tmp\xif_guarded_results.log'
$queue = Join-Path $Root 'tmp\xif_guarded_queue.txt'
$quarantine = Join-Path $Root 'tmp\xif_guarded_quarantine.txt'
$lines = @(Get-Content -LiteralPath $results -ErrorAction SilentlyContinue)
$last = @{}
foreach ($l in $lines) {
  if ($l -match '^EXIT=(\d+) FILE=(tmp/external/ported/\S+\.lean)') { $last[$Matches[2]] = [int]$Matches[1] }
}
$failed = @($last.Keys | Where-Object { $last[$_] -ne 0 })
$rules2 = @()
if (Test-Path $Rules) {
  foreach ($ln in (Get-Content -LiteralPath $Rules)) {
    if ($ln.Trim().Length -eq 0) { continue }
    if ($ln.Trim().StartsWith('#')) { continue }
    $p = $ln -split '\|\|', 2
    if ($p.Count -eq 2) { $rules2 = $rules2 + ,@($p[0], $p[1]) }
  }
}
Write-Output ('failed ported files=' + $failed.Count + ' rules=' + $rules2.Count)
$patched = @()
$fixed = 0
foreach ($rel in ($failed | Select-Object -First $MaxFiles)) {
  $abs = Join-Path $Root $rel
  if (-not (Test-Path $abs)) { continue }
  $txt = Get-Content -LiteralPath $abs -Raw
  $orig = $txt
  foreach ($r in $rules2) { try { $txt = [regex]::Replace($txt, $r[0], $r[1]) } catch { } }
  if ($txt -ne $orig) {
    if (-not $DryRun) { Set-Content -LiteralPath $abs -Value $txt -NoNewline -Encoding utf8 }
    $patched = $patched + $rel
    $fixed++
  }
}
if (-not $DryRun) {
  foreach ($rel in $patched) {
    $abs = Join-Path $Root $rel
    $oleRel = $rel -replace '\.lean$', '.olean'
    $oleDir = Join-Path (Join-Path $Root '.lake\build\lib\lean') (Split-Path $oleRel)
    if (-not (Test-Path $oleDir)) { New-Item -ItemType Directory -Force -Path $oleDir | Out-Null }
    (Get-Item $abs).LastWriteTime = Get-Date
  }
  if (Test-Path $quarantine) {
    $q = @(Get-Content -LiteralPath $quarantine | Where-Object { $_ -notmatch 'external/ported' -and $_ -notmatch 'external\\ported' })
    Set-Content -LiteralPath $quarantine -Value $q
  }
  $cur = @(Get-Content -LiteralPath $queue -ErrorAction SilentlyContinue | Where-Object { $_.Trim().Length -gt 0 })
  $added = 0
  foreach ($rel in $patched) { if ($cur -notcontains $rel) { Add-Content -LiteralPath $queue -Value $rel; $added++ } }
  Write-Output ('patched=' + $fixed + ' requeued=' + $added)
} else { Write-Output ('dryrun would patch=' + $fixed) }
