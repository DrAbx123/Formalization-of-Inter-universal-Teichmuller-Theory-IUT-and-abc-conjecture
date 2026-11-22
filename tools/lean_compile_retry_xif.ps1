param([int]$FileTimeoutSeconds = 600, [int]$MaxPasses = 6)
$root = 'D:\lean'
$queue = Join-Path $root 'tmp\xif_compile_queue.txt'
$log = Join-Path $root 'tmp\xif_retry.log'
$results = Join-Path $root 'tmp\xif_retry_results.log'
$failedPath = Join-Path $root 'tmp\xif_compile_failed.txt'
$tmpOut = Join-Path $root 'tmp\xif_retry_last.out'
$tmpErr = Join-Path $root 'tmp\xif_retry_last.err'
function Write-Log([string]$text) { $stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'; Add-Content -LiteralPath $log -Value ("[" + $stamp + "] " + $text) }
$lines = @()
if (Test-Path -LiteralPath $queue) { $lines = @(Get-Content -LiteralPath $queue | Where-Object { $_ -and $_.Trim().Length -gt 0 }); Set-Content -LiteralPath $queue -Value '' }
$seen = @{}
$pending = New-Object System.Collections.ArrayList
foreach ($raw in $lines) {
  $rel = $raw.Trim()
  if ([IO.Path]::IsPathRooted($rel)) { try { $rel = [IO.Path]::GetRelativePath($root, $rel) } catch {} }
  if ($seen.ContainsKey($rel)) { continue }
  $seen[$rel] = $true
  [void]$pending.Add($rel)
}
Write-Log ('retry driver started pending=' + $pending.Count)
for ($pass = 1; $pass -le $MaxPasses; $pass++) {
  if ($pending.Count -eq 0) { break }
  $next = New-Object System.Collections.ArrayList
  $success = 0
  foreach ($rel in $pending) {
    $file = Join-Path $root $rel
    if (-not (Test-Path -LiteralPath $file)) { Add-Content -LiteralPath $results -Value ("MISSING " + $rel); continue }
    $olean = Join-Path $root ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($rel, 'olean'))
    Remove-Item -LiteralPath $tmpOut,$tmpErr -ErrorAction SilentlyContinue
    $proc = Start-Process -FilePath 'lake' -ArgumentList @('env','lean','-j1','-R',$root,'-o',$olean,$file) -WorkingDirectory $root -NoNewWindow -PassThru -RedirectStandardOutput $tmpOut -RedirectStandardError $tmpErr
    $exited = $proc.WaitForExit($FileTimeoutSeconds * 1000)
    if (-not $exited) { try { $proc.Kill() } catch {}; $code = -999 } else { $code = $proc.ExitCode }
    Add-Content -LiteralPath $results -Value ("PASS=" + $pass + " EXIT=" + $code + " FILE=" + $rel)
    if ($code -eq 0) { $success++ } else {
      if (Test-Path -LiteralPath $tmpOut) { Get-Content -LiteralPath $tmpOut -Tail 80 | Add-Content -LiteralPath $results }
      if (Test-Path -LiteralPath $tmpErr) { Get-Content -LiteralPath $tmpErr -Tail 80 | Add-Content -LiteralPath $results }
      [void]$next.Add($rel)
    }
  }
  Write-Log ('pass=' + $pass + ' success=' + $success + ' remaining=' + $next.Count)
  $pending = $next
  if ($success -eq 0) { break }
}
Set-Content -LiteralPath $failedPath -Value ($pending -join [Environment]::NewLine)
Write-Log ('retry driver done failed=' + $pending.Count + ' see ' + $failedPath)
