#Requires -Version 7.0
# xif_citable_check.ps1 - static verification of a citable Lean claim.
# Checks: (1) source exists; (2) olean exists and is fresh vs source;
# (3) last results.log EXIT line for the file is EXIT=0;
# (4) the file actually DECLARES things (theorem/def/instance/...) and is not comment/doc-only;
# (5) optional probe file has EXIT=0 and its output shows trio/no-axiom evidence.
param(
  [Parameter(Mandatory = $true)][string]$File,
  [string]$Probe = '',
  [string]$Root = 'D:\lean'
)
$ErrorActionPreference = 'Continue'
$rel = $File -replace '\\','/'
if ([IO.Path]::IsPathRooted($rel)) { $rel = [IO.Path]::GetRelativePath($Root, $rel) -replace '\\','/' }
$src = Join-Path $Root $rel
$ole = Join-Path $Root ('.lake/build/lib/lean/' + [IO.Path]::ChangeExtension($rel, 'olean'))
$results = Join-Path $Root 'tmp/xif_guarded_results.log'
$reasons = @()
$verdict = 'CITABLE'
if (-not (Test-Path -LiteralPath $src)) { $reasons += 'SOURCE_MISSING'; $verdict = 'NOT_CITABLE' }
$fresh = $false
if (Test-Path -LiteralPath $ole) {
  $o = Get-Item -LiteralPath $ole; $s = Get-Item -LiteralPath $src -ErrorAction SilentlyContinue
  if ($s -and $o.LastWriteTime -ge $s.LastWriteTime) { $fresh = $true } else { $reasons += 'OLEAN_STALE' }
} else { $reasons += 'OLEAN_MISSING' }
if (-not $fresh) { $verdict = 'NOT_CITABLE' }
$lastExit = $null
if (Test-Path -LiteralPath $results) {
  $matches = Select-String -Path $results -Pattern ('EXIT=(-?\d+) FILE=' + [regex]::Escape($rel)) | Select-Object -Last 1
  if ($matches) { $lastExit = $matches.Line; if ($lastExit -notmatch '^EXIT=0 ') { $reasons += 'LAST_EXIT_NOT_ZERO'; $verdict = 'NOT_CITABLE' } }
  else { $reasons += 'NO_EXIT_LINE'; $verdict = 'NOT_CITABLE' }
}
$declCount = 0
if (Test-Path -LiteralPath $src) {
  $inComment = $false
  foreach ($line in (Get-Content -LiteralPath $src)) {
    if ($line -match '^\s*/-') { $inComment = $true }
    if ($inComment) { if ($line -match '-/') { $inComment = $false }; continue }
    if ($line -match '^\s*(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s') { $declCount++ }
  }
  if ($declCount -eq 0) { $reasons += 'NO_REAL_DECLARATIONS_DOC_ONLY'; $verdict = 'NOT_CITABLE' }
}
$probeOk = $null
if ($Probe -ne '') {
  $prel = $Probe -replace '\\','/'
  if ([IO.Path]::IsPathRooted($prel)) { $prel = [IO.Path]::GetRelativePath($Root, $prel) -replace '\\','/' }
  $pm = Select-String -Path $results -Pattern ('EXIT=(-?\d+) FILE=' + [regex]::Escape($prel)) | Select-Object -Last 1
  $sec = @()
  if ($pm) {
    $lines = Get-Content -LiteralPath $results
    $idx = -1
    for ($i = $lines.Count - 1; $i -ge 0; $i--) { if ($lines[$i] -match ('EXIT=(-?\d+) FILE=' + [regex]::Escape($prel))) { $idx = $i; break } }
    if ($idx -ge 0) { for ($i = $idx + 1; $i -lt $lines.Count; $i++) { if ($lines[$i] -match '^EXIT=') { break }; $sec += $lines[$i] } }
  }
  $hasTrio = ($sec -join "`n") -match 'propext'
  $hasNoAx = ($sec -join "`n") -match 'does not depend on any axioms'
  $hasSorry = ($sec -join "`n") -match 'sorryAx'
  if (-not $pm -or ($pm.Line -notmatch '^EXIT=0 ')) { $reasons += 'PROBE_NOT_GREEN'; $probeOk = $false }
  elseif (-not ($hasTrio -or $hasNoAx)) { $reasons += 'PROBE_NO_AXIOM_EVIDENCE'; $probeOk = $false }
  elseif ($hasSorry) { $reasons += 'PROBE_HAS_SORRYAX'; $probeOk = $false }
  else { $probeOk = $true }
  if ($probeOk -eq $false) { $verdict = 'NOT_CITABLE' }
}
[pscustomobject]@{
  verdict = $verdict;
  file = $rel;
  olean_fresh = $fresh;
  last_exit = ($lastExit -replace '^EXIT=(-?\d+).*','$1');
  declarations = $declCount;
  probe_ok = $probeOk;
  reasons = $reasons
} | ConvertTo-Json -Compress
if ($verdict -ne 'CITABLE') { exit 1 } else { exit 0 }