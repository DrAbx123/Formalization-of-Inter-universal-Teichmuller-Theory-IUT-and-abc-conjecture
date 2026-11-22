$p = Get-CimInstance Win32_Process -Filter "Name='node.exe'" | Where-Object { $_.CommandLine -match "dag_watchdog2" -and $_.CommandLine -notmatch "dsh-16g" }
if ($p) { exit 1 } else { exit 0 }
