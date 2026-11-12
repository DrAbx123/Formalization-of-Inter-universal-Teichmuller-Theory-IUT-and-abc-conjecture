# DAG-VALIDATION-NOTES — 2026-11-11 (shehdd)

validator: tools/dag_validate_decl2.mjs；完整报告 dag/DECLARATION-DAG-VALIDATION.json。

## 当前状态

- 最新（A468 后）：nodes 700 / edges 996-997 / problems 0 / proof 子图 700/700 acyclic。dag_clean2 报告：connected_components_before 17 -> 1（connectivity_edges 16）、remaining_isolated 0、attached_import_edges 122。statement/citation 子图环仅为 informational。
- shehdd 已修：bad kind statement->theorem（routes fragment，批量；新增节点会复现）、bad edge kind hierarchy->statement（iuti-ii fragment）、status PENDING-VERIFY->CONDITIONAL、9 节点 stale declarations 重写为源码出现 token、iuti-ii double-prefix 清理。
- 复发模式：routes fragment 新节点持续以 kind=statement 注册；shehdd 每轮用 tools/_shehdd_kind_fix.mjs 修正。建议 routes 作者直接写 kind=theorem 或 route。

## 剩余环

- 无（proof/interface/gap 子图 acyclic；旧 SCC {IUTII_LINK_GAP, STEPXI.CONTRACT} 随 owner fragment 重构消失）。

## 复现脚本（shehdd，均在 tools/）

- _shehdd_validator_fix.mjs — kind statement->theorem、status PENDING-VERIFY->CONDITIONAL、edge hierarchy->statement
- _shehdd_decl_shorten.mjs — declaration FQN -> 源码出现 token（validator src.includes 语义）
- _shehdd_fix_stale_decls.mjs — stale declarations 增补 + iuti-ii double-prefix 清理
- _shehdd_recurring_fix.mjs — 综合复发修正：kind statement->theorem、status PENDING-VERIFY->CONDITIONAL、edge hierarchy->statement、iuti-ii 前缀剥离
- _shehdd_kind_fix.mjs — 单点 kind 修正（等价子集）
- _shehdd_cycle_note.mjs — 环检测与 SCC 报告（含 gap 边）
- _shehdd_auto_probes.mjs — append-only probe 生成（scope 栈 + 注释剥离 + EOL 名支持）

流程（A468 起）: 改 fragment -> node tools/dag_merge3.mjs（写完自动跑 dag_clean2：schema 自愈 + 真实 import 接入 + 全图连通 + 环检查）-> node tools/dag_validate_decl2.mjs -> 读 dag/DECLARATION-DAG-VALIDATION.json 与 dag/DAG-CLEAN-REPORT.json。不要运行/依赖 dag_merge2 的未清理输出，也不要手写 declaration-dag.json。
