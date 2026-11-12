# CANONICAL DAG = OLEAN GROUND TRUTH (A479)

切换时间: 2026-11-11 (A479)。用户指令：开脚本把 DAG 完全重建、用 olean；选定方案 1（替换原 fragment DAG 作为唯一正式 DAG），随后继续推进实际。

## 结构
- 正式 DAG 文件: dag/declaration-dag.json（由 tools/dag_rebuild_from_olean.mjs 每次重建）
- 节点 = 有 .olean 的编译模块（status=PROVED, evidence=olean），declarations = 源码解析出的声明名
- 边 = 源码 import（statement, observed_source）；clean2 额外补 610 条 hierarchy 连通边（structural，非证明）
- 原 fragment 语义图备份: dag/declaration-dag.fragments-backup.json；fragments 不再参与正式 DAG（DAG_ALLOW_FRAGMENTS=1 可恢复旧行为）
- 语义规划目标: coord/ACTUAL-TARGETS.md / .json（从备份图提取 728 个可行动节点，按 region 分组）

## 当前规模（2026-11-11 03:45 UTC+8）
- 10,268 模块节点 / 23,116 import 边 / +610 hierarchy / 0 cycles / 1 component / validator problems 0
- 声明 103,659 个；olean 无源码 394 个（旧构建残留，已跳过）

## 工作方式（A479 起）
1) 不再手工维护 fragment 节点；DAG 只认真实编译产物（olean）
2) 实际推进 = 为 coord/ACTUAL-TARGETS.md 中的真实缺口写 Lean → 加 dag/watchdog/extra-targets.txt → watchdog 编译 → olean 出现即自动进 DAG
3) 质量纪律：真实数学定理/consumer，禁止 adapted 副本、List String 簿记、True/trivial 占位
4) 不碰 watchdog、不手动编译
## A480 (goal round 1) 更新
- 正式 DAG 重建加入 **sorry 审计**：逐模块扫描源码（剥离注释/字符串）中的真实 `sorry`；含 sorry 的模块 status=CONDITIONAL，其余 PROVED。
- 结果：10,284 模块 / 23,140 import 边 / PROVED 10,248 / CONDITIONAL 36（45 处真实 sorry；31 在 tmp/sheaf/n8/closure，5 在 tmp/sheaf/xif/paper）。
- 生成 `dag/SORRY-AUDIT.md` / `.json`；`dag_next` 现在 actionable=36 / ready=21（正是 sorry 模块，按依赖排序）。
- 365 个 stale 模块（源码新于 olean）已加入 extra-targets 排队重编（其中 287 个新入队）。
- 8 个 owner 已领本轮任务：sorry 消除（n8/xif）+ tmp 资产挖掘（repo-route-index 671 uncovered + tmp EXIT0/OLEAN_FRESH）+ 各区域前置对象真实证明。
## A480 补充：prerequisite scope 审计
- `tools/dag_scope_audit.mjs`：从 LeanFormal/IUT + Iut 全部模块出发走 import 闭包（1,213 模块）。
- 结果：**closure 1,213 / PROVED 1,213 / GAP 0 / CONDITIONAL 0 / sorry 模块 0 / sorry 出现 0 / axiom 声明模块 0**（`dag/PREREQ-SCOPE.md` / `.json`）。
- 全局 DAG 仍是 10,303 模块：PROVED 10,269 / GAP 34（n8 31 + xif 3，均有 DAG-BLOCKED 具体 no-go 原因）。