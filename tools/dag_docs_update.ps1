$root='D:\lean'
Set-Location $root
$p = Join-Path $root 'dag/README.md'
$c = Get-Content $p -Raw
$c = $c.Replace('- 当前：**716 节点 / 1,498 边 / 0 conflicts**', '- 当前：**63,577 节点 / 1,498 边 / 0 conflicts**')
$c = $c.Replace('| paper-theta: | EtTh/GenEll/AbsTopIII/NCBel/Hodge-Arakelov/Explicit estimates 的 paper 节点（383/1082） |', '| paper-theta: | EtTh/GenEll/AbsTopIII/NCBel/Hodge-Arakelov/Explicit estimates 的 paper 节点（383/1082） |' + [Environment]::NewLine + '| route-mentions: | **42,770 条路线/尝试/反例/障碍提及**（来自 9,515 个 md/txt 文档，含 AUDIT_LEDGER 3.4MB） |' + [Environment]::NewLine + '| paper-labels: | **20,091 个 paper 定理/定义/引理标签**（257 篇 corpus） |')
$c | Set-Content -NoNewline $p
$rp = Join-Path $root 'dag/DAG-REPORT.md'
$r = Get-Content $rp -Raw
$r = $r.Replace('| nodes | 716 |', '| nodes | 63,577 |')
$r = $r.Replace('| validator | **ok=true** (dag/DECLARATION-DAG-VALIDATION.json) |', '| validator | **ok=true** (dag/DECLARATION-DAG-VALIDATION.json) |' + [Environment]::NewLine + [Environment]::NewLine + 'Complete-universe additions: route-mentions fragment (42,770 nodes from 9,515 docs) + paper-labels fragment (20,091 nodes from 257 papers); no edges (evidence indexes attached to the route DAG).')
$r | Set-Content -NoNewline $rp
Write-Output 'docs updated'
$j = Get-Content (Join-Path $root 'dag/DECLARATION-DAG-VALIDATION.json') -Raw | ConvertFrom-Json
Write-Output ('decl nodes=' + $j.nodes + ' edges=' + $j.edges + ' ok=' + $j.validation.ok + ' problems=' + $j.problems.Count)
$f = Get-Content (Join-Path $root 'dag/DAG-VALIDATION.json') -Raw | ConvertFrom-Json
Write-Output ('file nodes=' + $f.file_graph.nodes + ' edges=' + $f.file_graph.edges + ' cycle=' + $f.file_graph.import_cycle + ' ok=' + $f.validation.ok)