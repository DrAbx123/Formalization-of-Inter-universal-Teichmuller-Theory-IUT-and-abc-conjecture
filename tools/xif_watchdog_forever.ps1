$ErrorActionPreference = 'Continue'
[Console]::OutputEncoding = [System.Text.UTF8Encoding]::new($false)
$root = 'D:\lean'
$queueScript = Join-Path $root 'tools\xif_guarded_queue.ps1'
$log = Join-Path $root 'tmp\xif_watchdog_forever.log'
$stopFlag = Join-Path $root 'tmp\xif_watchdog_stop.flag'
$pwsh = 'C:\Program Files\PowerShell\7\pwsh.exe'
function Write-ForeverLog([string]$text) {
  $stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'
  Add-Content -LiteralPath $log -Value ("[" + $stamp + "] " + $text)
}
$mutex = New-Object System.Threading.Mutex($false, 'Global\IUT_XIF_Watchdog_Forever')
if (-not $mutex.WaitOne(0)) {
  Write-ForeverLog ('secondary wrapper pid=' + $PID + ' exiting: primary already holds mutex')
  exit 0
}
Write-ForeverLog ('forever wrapper started pid=' + $PID)
try {
while (-not (Test-Path -LiteralPath $stopFlag)) {
  $existing = @(Get-CimInstance Win32_Process -ErrorAction SilentlyContinue | Where-Object {
    $_.CommandLine -and $_.CommandLine -match 'xif_guarded_queue\.ps1' -and $_.CommandLine -notmatch 'xif_watchdog_forever'
  })
  if ($existing.Count -eq 0) {
    Write-ForeverLog 'queue manager absent; starting it'
    & $pwsh -NoLogo -NoProfile -ExecutionPolicy Bypass -File $queueScript -MaxParallel 12 -FileTimeoutSeconds 900
    Write-ForeverLog ('queue manager exited code=' + $LASTEXITCODE)
  }
  Start-Sleep -Seconds 15
}
Write-ForeverLog 'stop flag present; forever wrapper exiting'
} finally {
  $mutex.ReleaseMutex()
  $mutex.Dispose()
}
