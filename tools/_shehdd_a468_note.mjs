import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/DAG-VALIDATION-NOTES.md';
let txt=readFileSync(p,'utf8');
txt=txt.replace(/流程: 改 fragment[^\n]*/, '流程（A468 起）: 改 fragment -> node tools/dag_merge3.mjs（写完自动跑 dag_clean2：schema 自愈 + 真实 import 接入 + 全图连通 + 环检查）-> node tools/dag_validate_decl2.mjs -> 读 dag/DECLARATION-DAG-VALIDATION.json 与 dag/DAG-CLEAN-REPORT.json。不要运行/依赖 dag_merge2 的未清理输出，也不要手写 declaration-dag.json。');
txt=txt.replace(/- 最新：[^\n]*/, '- 最新（A468 后）：nodes 700 / edges 996-997 / problems 0 / proof 子图 700/700 acyclic。dag_clean2 报告：connected_components_before 17 -> 1（connectivity_edges 16）、remaining_isolated 0、attached_import_edges 122。statement/citation 子图环仅为 informational。');
writeFileSync(p,txt);
console.log('notes updated for A468 merge3 workflow');
