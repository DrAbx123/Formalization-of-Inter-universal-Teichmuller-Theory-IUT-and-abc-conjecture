# Install the 16 GB host patch for DeepSeek Harness.
# It requires the app to be fully closed first.
$ErrorActionPreference = 'Stop'
$resources = 'D:\Users\Administrator\AppData\Local\Programs\DeepSeek Harness\resources'
$appAsar = Join-Path $resources 'app.asar'
$patched = Join-Path $resources 'app.asar.16g'
$backup = Join-Path $resources 'app.asar.orig-16g.bak'
$nodeExe = Join-Path $resources 'runtime\primary-runtime\dependencies\node\bin\node.exe'
$dshDir = Join-Path $resources 'dsh-16g'
$exe = 'D:\Users\Administrator\AppData\Local\Programs\DeepSeek Harness\DeepSeek Harness.exe'
$running = Get-Process -Name 'DeepSeek Harness' -ErrorAction SilentlyContinue
if ($running) { Write-Error 'DeepSeek Harness is still running. Close it completely, then run this installer again.'; exit 1 }
foreach ($p in @($patched, $nodeExe, $dshDir, $appAsar)) { if (-not (Test-Path -LiteralPath $p)) { Write-Error "Missing required path: $p"; exit 1 } }
if (-not (Test-Path -LiteralPath $backup)) { Copy-Item -LiteralPath $appAsar -Destination $backup }
Copy-Item -LiteralPath $patched -Destination $appAsar -Force
[Environment]::SetEnvironmentVariable('DSHN', $nodeExe, 'User')
[Environment]::SetEnvironmentVariable('DSHN', $nodeExe, 'Machine')
[Environment]::SetEnvironmentVariable('DSH_DESKTOP_HOST_', $dshDir, 'User')
[Environment]::SetEnvironmentVariable('DSH_DESKTOP_HOST_', $dshDir, 'Machine')
[Environment]::SetEnvironmentVariable('NODE_OPTIONS', '--max-old-space-size=16384', 'User')
[Environment]::SetEnvironmentVariable('NODE_OPTIONS', '--max-old-space-size=16384', 'Machine')
$env:DSHN = $nodeExe
$env:DSH_DESKTOP_HOST_ = $dshDir
$env:NODE_OPTIONS = '--max-old-space-size=16384'
Start-Process -FilePath $exe
Write-Output 'Installed and started DeepSeek Harness with the 16 GB host patch.'
Write-Output "Backup: $backup"
