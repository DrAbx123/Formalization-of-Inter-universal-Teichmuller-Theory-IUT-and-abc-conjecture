# A480: SORRY-AUDIT 交叉核对（shehdd；按 Lean 词法去注释/字符串）

方法: 对 dag/SORRY-AUDIT.md 的 36 模块做字符级 Lean 词法扫描（嵌套块注释/行注释/字符串/字符字面量），只统计源码中的 sorry token。

- 审计文件: 36 模块 / 45 处。
- **真实源码 sorry total = 37**。

| file | audit | 真实 sorry | 说明 |
|---|---|---|---|
| tmp/sheaf/n8/closure/C5Native.lean | 2 | 1 | 部分为文案或已修复 |
| tmp/sheaf/n8/closure/FiniteObservationHull.lean | 1 | 0 | 纯文案字符串/已修复，无需处理 |
| tmp/sheaf/n8/closure/IPLFamilyData.lean | 1 | 0 | 纯文案字符串/已修复，无需处理 |
| tmp/sheaf/n8/closure/P6ChainA.lean | 1 | 0 | 纯文案字符串/已修复，无需处理 |
| tmp/sheaf/n8/closure/P6RelaxedGlobalReadout.lean | 1 | 0 | 纯文案字符串/已修复，无需处理 |
| tmp/sheaf/n8/closure/P6SHEInd.lean | 1 | 0 | 纯文案字符串/已修复，无需处理 |
| tmp/sheaf/xif/paper/IUTExternal32GateV36Actual.lean | 1 | 0 | 纯文案字符串/已修复，无需处理 |
| tmp/sheaf/xif/paper/S2748AbsNormGeRationalPrimeActual.lean | 1 | 0 | 纯文案字符串/已修复，无需处理 |

## 结论

- 假阳性（真实 0）: 见上表；不计入修复任务。
- 真实 sorry 仍集中在 n8 closure 与 paper 模块；对应 OBSTRUCTION 已在 coord/DAG-BLOCKED.json 登记，修复优先级见 coord/N8-SORRY-TRIAGE-A480.md。
- 建议: SORRY-AUDIT 生成器改用同样词法过滤，避免 ledger 文案混入统计。

