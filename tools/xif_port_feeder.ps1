<#
.SYNOPSIS
  Feed ported external files to the watchdog queue in dependency order, only when their
  local import oleans are already fresh. Prevents "object file not found" churn.
.DESCRIPTION
  Reads the topological table from <Dir>/import_chain.md (| # | depth | file | ...),
  checks each not-yet-fresh file's local (tmp.*) imports against .lake/build/lib/lean,
  and appends ready files (up to -MaxAdd) to the watchdog queue.
.EXAMPLE
  tools/xif_port_feeder.ps1 -Dir D:\lean\tmp\external\ported\tauceti2 -MaxAdd 30
#>
param(
  [string]$Dir = 'D:\lean\tmp\external\ported\tauceti2',
  [string]$Root = 'D:\lean',
  [int]$MaxAdd = 30,
  [switch]$CleanPortEntries,
  [switch]$DryRun
)
$ErrorActionPreference = 'Continue'
function Add-QueueLine([string]$line) {
  for ($i = 0; $i -lt 5; $i++) {
    try { Add-Content -LiteralPath $queue -Value $line -ErrorAction Stop; return $true } catch { Start-Sleep -Milliseconds (300 * ($i + 1)) }
  }
  return $false
}
function Set-QueueLines([string[]]$lines) {
  for ($i = 0; $i -lt 5; $i++) {
    try { Set-Content -LiteralPath $queue -Value $lines -ErrorAction Stop; return $true } catch { Start-Sleep -Milliseconds (300 * ($i + 1)) }
  }
  return $false
}

$queue = Join-Path $Root 'tmp\xif_guarded_queue.txt'
$chain = Join-Path $Dir 'import_chain.md'
if (-not (Test-Path $chain)) { Write-Output 'NO import_chain.md'; exit 1 }
$relDir = [System.IO.Path]::GetRelativePath($Root, $Dir) -replace '\\','/'
$order = @()
foreach ($ln in (Get-Content -LiteralPath $chain)) {
  if ($ln -match '^\|\s*\d+\s*\|\s*\d+\s*\|\s*([^|]+?)\s*\|') { $order += ($relDir + '/' + $Matches[1].Trim()) }
}
$order = @($order | Select-Object -Unique)
Write-Output ('topo files=' + $order.Count)
$cur = @(Get-Content -LiteralPath $queue -ErrorAction SilentlyContinue | Where-Object { $_.Trim().Length -gt 0 })
if ($CleanPortEntries) {
  $prefix = $relDir + '/'
  $keep = @($cur | Where-Object { -not $_.Replace('\','/').StartsWith($prefix) })
  if (-not $DryRun) { [void](Set-QueueLines $keep) }
  Write-Output ('cleaned queue entries: ' + ($cur.Count - $keep.Count))
  $cur = $keep
}
function Get-LocalImports([string]$rel) {
  $abs = Join-Path $Root $rel
  $mods = @()
  if (-not (Test-Path $abs)) { return $mods }
  $head = @(Get-Content -LiteralPath $abs -TotalCount 60 -ErrorAction SilentlyContinue)
  foreach ($l in $head) {
    if ($l -match '^(?:public |private |protected )?import (.+)$') {
      foreach ($m in ($Matches[1].Trim() -split '\s+')) { if ($m.StartsWith('tmp.') -or $m.StartsWith('LeanFormal.') -or $m.StartsWith('Iut.')) { $mods += $m } }
    }
  }
  return $mods
}
function OLeanFresh([string]$mod) {
  $rel = ($mod -replace '\.','/') + '.olean'
  $p = Join-Path (Join-Path $Root '.lake\build\lib\lean') $rel
  $src = Join-Path $Root (($mod -replace '\.','/') + '.lean')
  if (-not (Test-Path $p)) { return $false }
  if (Test-Path $src) { return ((Get-Item $p).LastWriteTime -ge (Get-Item $src).LastWriteTime) }
  return $true
}
$added = 0
foreach ($rel in $order) {
  if ($added -ge $MaxAdd) { break }
  $abs = Join-Path $Root $rel
  if (-not (Test-Path $abs)) { continue }
  $oleRel = $rel -replace '\.lean$', '.olean'
  $ole = Join-Path (Join-Path $Root '.lake\build\lib\lean') $oleRel
  if ((Test-Path $ole) -and ((Get-Item $ole).LastWriteTime -ge (Get-Item $abs).LastWriteTime)) { continue }
  if ($cur -contains $rel) { continue }
  $deps = Get-LocalImports $rel
  $ready = $true
  foreach ($d in $deps) { if (-not (OLeanFresh $d)) { $ready = $false; break } }
  if (-not $ready) { continue }
  if (-not $DryRun) { [void](Add-QueueLine $rel) }
  $cur += $rel
  $added++
}
Write-Output ('fed=' + $added)
