import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/DAG-VALIDATION-NOTES.md';
const lines=[
'# DAG-VALIDATION-NOTES — 2026-11-11 (shehdd)',
'',
'validator: tools/dag_validate_decl2.mjs；完整报告 dag/DECLARATION-DAG-VALIDATION.json。',
'',
'## 当前状态',
'',
'- 最新：nodes 580 / edges 628 / problems 1（仅 proof/interface/gap 子图环，topo 576/580）。',
'- shehdd 已修：bad kind statement->theorem（routes fragment，批量；新增节点会复现）、bad edge kind hierarchy->statement（iuti-ii fragment）、status PENDING-VERIFY->CONDITIONAL、9 节点 stale declarations 重写为源码出现 token、iuti-ii double-prefix 清理。',
'- 复发模式：routes fragment 新节点持续以 kind=statement 注册；shehdd 每轮用 tools/_shehdd_kind_fix.mjs 修正。建议 routes 作者直接写 kind=theorem 或 route。',
'',
'## 剩余环（未改边，需 owner 语义决策）',
'',
'- SCC size=2: iutiii:IUTIII.IUTII_LINK_GAP, iutiii:IUTIII.STEPXI.CONTRACT',
'- 边：CONTRACT -> IUTII_LINK_GAP [gap]；IUTII_LINK_GAP -> CONTRACT [interface]。',
'- 解释：contract 构造依赖 link gap（gap 边），typed link 接口又依赖 contract 类型（interface 边），形成认知双向依赖。修复需确认哪条边方向/类别错误，未确认前保留现状。',
'',
'## 复现脚本（shehdd，均在 tools/）',
'',
'- _shehdd_validator_fix.mjs — kind statement->theorem、status PENDING-VERIFY->CONDITIONAL、edge hierarchy->statement',
'- _shehdd_decl_shorten.mjs — declaration FQN -> 源码出现 token（validator src.includes 语义）',
'- _shehdd_fix_stale_decls.mjs — stale declarations 增补 + iuti-ii double-prefix 清理',
'- _shehdd_kind_fix.mjs — 复发 routes kind=statement 单点修正',
'- _shehdd_cycle_note.mjs — 环检测与 SCC 报告（含 gap 边）',
'- _shehdd_auto_probes.mjs — append-only probe 生成（scope 栈 + 注释剥离 + EOL 名支持）',
'',
'流程: 改 fragment -> node tools/dag_merge3.mjs -> node tools/dag_validate_decl2.mjs -> 读 dag/DECLARATION-DAG-VALIDATION.json。',
''
];
writeFileSync(p, lines.join('\n'));
console.log('rewritten DAG-VALIDATION-NOTES.md');
