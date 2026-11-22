import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/DAG-VALIDATION-NOTES.md';
let txt=readFileSync(p,'utf8');
const add='\n## 复现脚本（shehdd）\n\n- tools/_shehdd_validator_fix.mjs — kind statement->theorem、status PENDING-VERIFY->CONDITIONAL、edge hierarchy->statement；\n- tools/_shehdd_decl_shorten.mjs — declaration FQN->源码出现 token（validator 的 src.includes 语义）；\n- tools/_shehdd_fix_stale_decls.mjs — stale declarations 增补与 iuti-ii double-prefix 清理；\n- tools/_shehdd_kind_fix.mjs — 复发 routes kind=statement 的单点修正；\n- tools/_shehdd_cycle_note.mjs — 环检测与 SCC 报告（含 gap 边）；\n- tools/_shehdd_auto_probes.mjs — append-only probe 生成（namespace+section scope 栈、注释剥离、EOL 名支持）。\n\n流程：改 fragment -> node tools/dag_merge3.mjs -> node tools/dag_validate_decl2.mjs -> 读取 dag/DECLARATION-DAG-VALIDATION.json。\n';
if(!txt.includes('## 复现脚本')) txt+=add;
writeFileSync(p,txt);
console.log('repro section appended');
