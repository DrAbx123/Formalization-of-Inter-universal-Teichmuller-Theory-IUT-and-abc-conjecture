$root='D:\lean'; Set-Location $root
$p = Join-Path $root 'dag/README.md'
$c = Get-Content $p -Raw
$section = @(
'',
'## 动态维护（DAG watchdog，替代 queue）',
'',
'- **入口**：`tools/dag_watchdog2.mjs`（后台常驻；当前由 pwsh 进程守护）',
'- **循环**：',
'  1. 每 5 分钟重建 Layer A 图（`dag_build.mjs`+`dag_validate.mjs`）并合并 Layer B（`dag_merge3.mjs`+`dag_validate_decl2.mjs`），再计算运行时证据（`dag_status.mjs` → `runtime-status.json`/`RUNTIME-MISMATCH.md`）',
'  2. 生成 dirty 计划（`dag_plan.mjs`+`dag_plan_deps.mjs`）：源文件比 olean 新、或多个 PROVED/BOTTOM 节点的证据不新鲜（mismatch）',
'  3. **按 import 依赖拓扑序**编译 dirty（依赖先）；并发上限 **12 个 lean 进程**（`DAG_MAX`，用户要求最多 12）',
'  4. 每个文件结果以 `EXIT=n FILE=rel` 追加到 `tmp/xif_guarded_results.log`（兼容既有 checker），并写入 `dag/watchdog/logs/`',
'  5. 失败文件记录在 `state.json`，同一源版本 10 分钟内不重试；源变更后自动重试',
'- **不再使用 queue**：`xif_guarded_queue`/`xif_watchdog_forever` 已停止；DAG watch dog 是唯一编译调度器',
'- **产出**：`dag/watchdog/{plan,order,runtime-status,heartbeat,state}.json`、`watchdog.log`、`stdout.log`、`RUNTIME-MISMATCH.md`、`logs/`',
'- **动态性**：新文件/新 import 会在图重建时自动进入；声明级 fragment 更新后 merge 自动更新节点；证据变化会反映到 mismatch 报告'
)
$c = $c + [Environment]::NewLine + ($section -join [Environment]::NewLine)
$c | Set-Content -NoNewline $p
Write-Output 'README updated'
Write-Output '=== throttle check ==='
Select-String -Path tools/dag_watchdog2.mjs -Pattern '_st=state' | Select-Object -First 1 | ForEach-Object { Write-Output 'THROTTLE PRESENT' }
Write-Output '=== watchdog alive ==='
Get-CimInstance Win32_Process -Filter "Name='pwsh.exe'" | ForEach-Object { if ($_.CommandLine -match 'dag_watchdog2') { Write-Output ('PID ' + $_.ProcessId) } }
Get-Content dag\watchdog\watchdog.log -Tail 3