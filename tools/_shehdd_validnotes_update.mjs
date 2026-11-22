import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/DAG-VALIDATION-NOTES.md';
let txt=readFileSync(p,'utf8');
txt=txt.replace(/## 当前状态[\s\S]*?## 剩余环/, '## 当前状态\n\n- 最新 validator：nodes 576 / edges 628 / problems 1（仅 proof/interface/gap 子图环，topo 572/576）。\n- 已由 shehdd 修复 46 类问题：bad kind statement->theorem（routes fragment 批量，后续新增节点会复现，见下）、bad edge kind hierarchy->statement、status PENDING-VERIFY->CONDITIONAL、9 节点 stale declarations 重写为源码出现 token、iuti-ii double-prefix 清理。\n- **复发模式**：routes fragment 的新节点持续以 kind=statement 注册（作者脚本），shehdd 每轮自动修正为 theorem；建议 routes 作者直接写 kind=theorem 或 route。\n\n## 剩余环');
writeFileSync(p,txt);
console.log('notes updated');
