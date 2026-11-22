import { appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const add = ['','## 5. A484 队列工具规则补充（本轮更新）','','- 以后新增编译目标统一用: node tools/extras_add.mjs tmp/sheaf/xif/paper/YourFileActual.lean（加锁/去重/校验/原子写），不再直接编辑 extra-targets.txt。','- 队列当前 439 条；P1FinitePartActual 根 EXIT=0；f4b 链下游已重新入队（StepProviderPrime*/P1StepProvider*/P1FinitePartMeasure 等 12+ 条，等 watchdog 按依赖重编）。','- 我的 green rung 资产（FourTriangleAssembly/CV/F4b/IndRoute/Ind2/HeightVolume/FreyReduction/L02 等）仍按规则 2 直接复用，不入队。','- 本轮未新增队列条目、未新建 Lean；审计结论不变。',''];
appendFileSync(ROOT+'/coord/A484-RUNG-QUEUE-AUDIT-shehdd.md', add.join('\n'));
console.log('addendum appended');
