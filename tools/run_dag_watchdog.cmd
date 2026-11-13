@echo off
cd /d D:\lean
set DAG_MAX=12
set DAG_SEEDS=extra
set DAG_CYCLE_MS=5000
set DAG_GRAPH_MS=3600000
node D:\lean\tools\dag_watchdog2.mjs >> D:\lean\dag\watchdog\stdout.log 2>&1


