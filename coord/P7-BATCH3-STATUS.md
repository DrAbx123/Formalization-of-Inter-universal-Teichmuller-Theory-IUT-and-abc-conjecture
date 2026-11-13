# P7 第三批（abc lane）— 5 份 Lean，待 Lead 加名单

| 文件 | 内容 |
|---|---|
| `Mzk1Cor312SignedArithmeticActual.lean` | signed target 算术：`-A≤-R ↔ 0≤A−R ↔ R≤A`；`q≤θ` 与 `M≥0` 的换算（含 hq/hθ） |
| `Mzk1ArchFactorProductActual.lean` | `(1/(2l))·(2l)=1`（l≠0）；`1/(2l)=1 ↔ l=1/2`（区分 q 因子与 arch 因子 1） |
| `Mzk1HullBoundAddTransferActual.lean` | `mainTerm=(1/4)l(log d+log f)`；C0 单调转移与 total 转移（#7） |
| `Mzk1ComparisonTargetInterfaceActual.lean` | `MTargetNonneg := 0≤A−R`、`SignedTarget := -A≤-R` 及等价（#1） |
| `Mzk1P7CountsActual.lean` | 7 missing 的计数：partial=3、still=4、discharged=0（audit-only） |

全部 header interface/audit；无 sorry/axiom、无新假设。