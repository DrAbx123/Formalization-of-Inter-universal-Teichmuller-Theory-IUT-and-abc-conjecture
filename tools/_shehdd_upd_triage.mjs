import { readFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/N8-SORRY-TRIAGE-A480.md';
let txt=readFileSync(p,'utf8');
if(!txt.includes('## A480 执行更新')){
  const add=['','## A480 执行更新（与 coord/DAG-BLOCKED.json 对齐）','',
  '- 核对: coord/DAG-BLOCKED.json 已有 31 条 sorries:n8-closure:* 条目（hull owner 登记的 OBSTRUCTION 原因），与本 triage 的 31 模块一一对应，无需重复登记。',
  '- 已修复: FiniteObservationHull、IPLFamilyData（A480 真实证明），C5Native 部分修复；其余 n8 sorry 模块维持 CONDITIONAL + blocked 原因（缺 production donor / 缺 actual data package），不删历史。',
  '- 修复优先级不变: Tier1 = NativeC3, C3TensorConstruction, P6ChainA, SourceAllowedOutputActualAttempt（有 n8 外部 paper 层消费者）；Tier2 仅在 n8 route 重启时处理；Tier4 三模块由 blocked 记录归档。',''];
  appendFileSync(p, add.join('\n'));
  console.log('triage doc updated');
} else console.log('already updated');
