$ErrorActionPreference = 'Stop'
$root = 'D:\lean'
$pwsh = 'C:\Program Files\PowerShell\7\pwsh.exe'
$wrapper = Join-Path $root 'tools\xif_watchdog_forever.ps1'
$log = Join-Path $root 'tmp\xif_watchdog_forever.log'
$cmd = '"' + $pwsh + '" -WindowStyle Hidden -NoLogo -NoProfile -ExecutionPolicy Bypass -File "' + $wrapper + '"'
$res = Invoke-CimMethod -ClassName Win32_Process -MethodName Create -Arguments @{ CommandLine = $cmd; CurrentDirectory = $root }
$stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'
Add-Content -LiteralPath $log -Value ("[" + $stamp + "] launcher spawned wrapper pid=" + $res.ProcessId + " return=" + $res.ReturnValue)
