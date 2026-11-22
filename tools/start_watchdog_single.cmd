@echo off
cd /d D:\lean
powershell -NoProfile -Command "if (Get-CimInstance Win32_Process | Where-Object { $_.Name -eq 'node.exe' -and $_.CommandLine -match 'dag_watchdog2.mjs' -and $_.CommandLine -notmatch 'runner.js' }) { exit 0 } else { exit 1 }"
if not errorlevel 1 (
  echo watchdog already running
  exit /b 0
)
del /q D:\lean\dag\watchdog\watchdog.lock 2>nul
set DAG_MAX=10
set DAG_SEEDS=extra
set DAG_CYCLE_MS=5000
set DAG_GRAPH_MS=3600000
node D:\lean\tools\dag_watchdog2.mjs >> D:\lean\dag\watchdog\stdout.log 2>&1
