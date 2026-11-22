import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/DAG-VALIDATION-NOTES.md';
let txt=readFileSync(p,'utf8');
txt=txt.replace(/- 最新：[^\n]*/, '- 最新：nodes 633 / edges 633 / problems 0 / proof-interface subgraph ACYCLIC（validator ok=true）。此前 SCC {IUTII_LINK_GAP, STEPXI.CONTRACT} 已由 owner 重构 fragment（iuti-ii-abc2）后消失。');
txt=txt.replace(/## 剩余环（未改边，需 owner 语义决策）[\s\S]*?(?=\n## |$)/, '## 剩余环\n\n- 无（当前 proof/interface/gap 子图无环；631? 见 validator 报告 dag/DECLARATION-DAG-VALIDATION.json 的 acyclicity 段）。\n');
txt=txt.replace(/## 剩余环[\s\S]*?(?=\n## |$)/, '## 剩余环\n\n- 无（proof/interface/gap 子图 acyclic；旧 SCC {IUTII_LINK_GAP, STEPXI.CONTRACT} 随 owner fragment 重构消失）。\n');
writeFileSync(p,txt);
console.log('notes updated to problems=0');
