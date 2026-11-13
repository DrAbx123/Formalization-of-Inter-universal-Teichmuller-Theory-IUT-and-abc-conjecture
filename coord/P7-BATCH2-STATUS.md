# P7 第二批（abc lane）— 5 份 Lean，待 Lead 加名单

| 文件 | 内容 |
|---|---|
| `Mzk1ComparisonGapArithmeticActual.lean` | #1 算术：`q≤θ ↔ 0≤θ−q ↔ −θ≤−q ↔ 0≤A−R`（纯 linarith） |
| `Mzk1GeneralComparisonInterfaceActual.lean` | #1 named Prop `GeneralQThetaComparison q θ := q ≤ θ` + iff + conditional consumer（GAP，不声称证明） |
| `Mzk1StepXIEvidenceLinkActual.lean` | #6 linkage schema：三义务 → StepXIEvidenceInterface 字段；GAP-P7-CONTRACT（schema only） |
| `Mzk1IQCarrierStatusActual.lean` | #2 状态表 4 行（A481 green / literal missing / C3 gap / C6 clue） |
| `Mzk1HullUpperBoundTransferActual.lean` | #7 转移算术：`HullUpperBound C0` + `C0≤C1` ⇒ `C1`；`C0=0`+主项非负 ⇒ `0≤V` |

全部 header 标 GAP/interface，无 sorry/axiom、无新假设。