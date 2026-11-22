$root='D:\lean'; Set-Location $root
$p = Join-Path $root 'dag/README.md'; $c = Get-Content $p -Raw
$c = $c.Replace('- 当前：**63,577 节点 / 1,498 边 / 0 conflicts**', '- 当前：**63,606 节点 / 1,519 边 / 0 conflicts**')
$c = $c.Replace('| paper-labels: | **20,091 个 paper 定理/定义/引理标签**（257 篇 corpus） |', '| paper-labels: | **20,091 个 paper 定理/定义/引理标签**（257 篇 corpus） |' + [Environment]::NewLine + '| web-routes: | **12 条外部（网络）路线**：LANA 项目/中期报告、IUT Validation、Bridge Certificate（4 applications）、IUT Comes Home、Joshi FAQ、Scholze-Stix 报告、Hayashi impossibility、Mochizuki Formalization 报告、LeanForm ZFC、autoformalization、IUAni 动画 |')
$c | Set-Content -NoNewline $p
$rp = Join-Path $root 'dag/DAG-REPORT.md'; $r = Get-Content $rp -Raw
$r = $r.Replace('| nodes | 63,577 |', '| nodes | 63,606 |')
$r = $r.Replace('Complete-universe additions: route-mentions fragment', 'Online routes: 12 external route candidates (LANA project/interim report; IUT Validation; Bridge Certificate with 4 applications; IUT Comes Home; Joshi FAQ; Scholze-Stix report; Hayashi impossibility; Mochizuki Formalization report; LeanForm ZFC; autoformalization; IUAni animations), status=EXTERNAL, evidence-only (no proof claims). Complete-universe additions: route-mentions fragment')
$r | Set-Content -NoNewline $rp
Write-Output 'docs updated'
$j = Get-Content (Join-Path $root 'dag/DECLARATION-DAG-VALIDATION.json') -Raw | ConvertFrom-Json
Write-Output ('decl nodes=' + $j.nodes + ' edges=' + $j.edges + ' ok=' + $j.validation.ok)