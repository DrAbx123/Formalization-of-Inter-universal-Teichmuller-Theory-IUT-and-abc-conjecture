@echo off
cd /d D:\lean
set DAG_MAX=8
set DAG_SEEDS=extra
set DAG_CYCLE_MS=1000
set DAG_GRAPH_MS=3600000
"D:\Users\Administrator\AppData\Local\Programs\DeepSeek Harness\resources\runtime\primary-runtime\dependencies\node\bin\node.exe" D:\lean\tools\dag_watchdog2.mjs >> D:\lean\dag\watchdog\stdout7.log 2>&1
