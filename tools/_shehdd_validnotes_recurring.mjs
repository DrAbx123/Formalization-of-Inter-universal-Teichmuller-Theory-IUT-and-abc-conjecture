import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/DAG-VALIDATION-NOTES.md';
let txt=readFileSync(p,'utf8');
txt=txt.replace(/- _shehdd_kind_fix\.mjs[^\n]*/, '- _shehdd_recurring_fix.mjs — 综合复发修正：kind statement->theorem、status PENDING-VERIFY->CONDITIONAL、edge hierarchy->statement、iuti-ii 前缀剥离\n- _shehdd_kind_fix.mjs — 单点 kind 修正（等价子集）');
txt=txt.replace(/- 最新：[^\n]*/, '- 最新：nodes 609 / edges 632 / problems 1（proof/interface/gap 子图环；SCC 见下）。并发新增节点会周期性引入 kind=statement / PENDING-VERIFY / iuti-ii 前缀复发，shehdd 每轮用 _shehdd_recurring_fix.mjs 清理。');
writeFileSync(p,txt);
console.log('notes updated');
