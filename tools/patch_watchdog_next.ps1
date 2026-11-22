$root='D:\lean'
Set-Location $root
$f='tools/dag_watchdog2.mjs'
$c=Get-Content $f -Raw
$a1="runTool('tools/dag_status.mjs'); lastGraph=Date.now(); }"
$b1="runTool('tools/dag_status.mjs'); runTool('tools/dag_next.mjs'); lastGraph=Date.now(); }"
$a2="await batch(); runTool('tools/dag_status.mjs');"
$b2="await batch(); runTool('tools/dag_status.mjs'); runTool('tools/dag_next.mjs');"
$c=$c.Replace($a1,$b1)
$c=$c.Replace($a2,$b2)
$c | Set-Content -NoNewline $f
Write-Output 'watchdog patched'
$p='dag/README.md'
$r=Get-Content $p -Raw
$old='- **动态性**：新文件/新 import 会在图重建时自动进入；声明级 fragment 更新后 merge 自动更新节点；证据变化会反映到 mismatch 报告'
$new='- **动态性（全自动）**：新文件/新 import 在每 5 分钟图重建时自动进入；teammates 更新 fragment 后 merge 自动刷新节点/状态/边；运行时证据（olean freshness/last_exit）自动写入 runtime-status；coord/DAG-NEXT.md 与 dag/watchdog/next.json 每个 rebuild/cycle 自动刷新；blocked/refuted/detoured 由 coord/DAG-BLOCKED.json 自动排除。'
$r=$r.Replace($old,$new)
$r | Set-Content -NoNewline $p
Write-Output 'readme updated'
Select-String -Path $f -Pattern 'dag_next' | ForEach-Object { Write-Output ('PATCHED: ' + $_.Line.Substring(0,[Math]::Min(100,$_.Line.Length))) }