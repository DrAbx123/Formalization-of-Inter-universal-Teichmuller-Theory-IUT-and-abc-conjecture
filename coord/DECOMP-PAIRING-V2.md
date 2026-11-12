# Decomposition pairing candidates v2 (A996)

| field | value |
|---|---|
| Status | PARTIAL (无候选对实际数据成立；目标 v2 严格取 variant 形式) |
| 目标 | M := A - R >= 0，A = |log q|/(2*l)，R = |log Theta|（NOT SSIneq） |
| 判定点 | 需给出 M 的显式展开并证明任一候选的逐项（或分组）不等式；当前全部 OPEN |
| 版本钉住 | lana 按根 Iut/ 树 + 行号；未手动编译；本文档不写入任何证明 |

## 0. 目标与显式展开来源

目标（variant）：M := A - R >= 0，A = |log q|/(2*l)，R = |log Theta|。
**禁止**使用 SSIneq/PaperNormVerdict/variant 作为目标或假设（见 §4 自检）。

R 的局部展开按 hull `coord/DECOMP-R-LOCAL.md`（packetVol 链）：
- R = -rhs，rhs = RHSData.rhs = R.vol.processionVol R.thetaHull（Iut/Cor312/RightHandSide.lean:107）；
- processionVol R = (sum i : Fin D.proc.length, globalVol (R i)) / D.proc.length（Iut/Cor312/LogVolume.lean:207），D.proc.length = l* = (l-1)/2；
- globalVol (R i) = sum^fin vQ, packetVol i vQ ((R i).region vQ)（LogVolume.lean:177）；
- packetVol_product（LogVolume.lean:130）：对非空 component，packetVol i vQ (productRegion U) = sum c, (prod j, weight vQ (c j)) * componentVol i vQ c (U c)；
- packetWeight i vQ c = prod j, weight vQ (c j)（LogVolume.lean:141），packetWeight_pos（:153），weight_sum_one（:88）。

因此 elementary 指标集 (vQ, i, c, j)，j 遍历 capsule i 的 labels；显式：
```
rhs = (1/nC) * sum_i sum_vQ sum_c P_{i,vQ,c},
P_{i,vQ,c} := packetWeight i vQ c * componentVol i vQ c (U_{i,vQ,c}),
R = -rhs,   M = A + rhs = A + (1/nC) * sum_i sum_vQ sum_c P_{i,vQ,c}.
```
这是 M 的唯一展开口径：A 与 P 项都在同一边（无移项重排）。

## 1. 每项的独立非负来源（或负号）

| 项 | 符号 | 独立非负/符号来源（stepxi DECOMP-POSITIVE-TERMS 清单） |
|---|---|---|
| A = |log q|/(2l) | >= 0 | 定义（LeftHandSide.lean:81-88 absLogQ = logQ/(2*l)）；q != 0 green |
| packetWeight i vQ c | > 0 | LogVolume.lean:153 packetWeight_pos（PROVED） |
| tame finite componentVol: sum_j (1 - 1/e_cj) log p | >= 0 | VcI.lean:435 componentVol_leastHull_tensorLogShell_eq_tame；e >= 1 |
| q-scaling piece: - sum_j j^2 * ord_p(q) * log p（scaled shell 部分） | <= 0 | scaleElt 单位缩放保持 least hull（leastHull_units_smul）；componentVol 缩放律 |
| archDefect（无穷位） | >= 0 | Gap.lean:463 archDefect_nonneg |
| shellDefect | >= 0 | Gap.lean:442 shellDefect_nonneg |
| ind2Term | >= 0 | Gap.lean:756 ind2Term_nonneg（componentVol_le_of_subset；lgpComp_subset_theta） |
| gapTerm / gapAt / gap / gapNoHull | >= 0 | Gap.lean:646/657/514/579（但注意：这些是 logVol 与 rhs 的差，属于 SSIneq 的 gap 分解，**不一定是 M=A-R 的项**，见 §3 禁止项） |
| orderVol | <= 0 | VcI.lean:102 orderVol_nonpos |
| defectPacket | >= 0 | VcI.lean:770 defectPacket_nonneg |

关键符号结论：**q-scaling piece 是 M 中唯一的负贡献**，其量级为 `sum_j j^2 * ord_p(q) * log p`；而 A_p 的量级是 `ord_p(q) * log p / (2l)`。若两者要在 M 中相配，必须先证明缩放常数归一化的恒等式——当前**未证**，是中心 GAP。

## 2. 候选（Lean 陈述草案 + 显式展开）

### V2-C1: 逐坏位 A_p 与负 q-scaling 项配对（PARTIAL/GAP）
```
def QScalingPiece (p) : R := sum_j (j^2 : R) * ord_p(q) * log p   -- <= 0 in M
def V2C1 (p) : Prop := QScalingPiece p <= (2*l) * A_p           -- A_p = ord logp/(2l)
theorem v2c1_implies_M : (forall p, V2C1 p) -> 0 <= M            -- 需先给 M 的 P 展开
```
来源：tame 展开 VcI.lean:435 给正的部分；负部分是 scaling 律。
循环自检：V2C1 不含 SSIneq/variant/PaperNormVerdict；仅用 ord/log/scaleElt。GAP：缩放常数归一化 `(2l)*A_p` 与 lana 的 `(2l)` 归一化是否一致**未证**（左端 j^2 加权和为 `(2l)^2` 量级，不是 `2l`；系数必须由 packetWeight 归一化给出）。

### V2-C2: componentVol 正部按 (i,vQ,c) 分组（MODEL/PARTIAL）
```
def V2C2 (i vQ) : Prop := (sum_c P_{i,vQ,c} >= 0)
theorem v2c2_implies_M : (forall i vQ, V2C2 i vQ) -> 0 <= M
```
来源：packetWeight_pos + tame componentVol 非负；但 componentVol 含 scaling 负项，V2C2 等价于该 group 的负项被 tame/arch 正项覆盖。
循环自检：不含目标；正项必须来自 §1 表（tame/arch/ind2/defectShell），不得把 gap 项搬进来充数。

### V2-C3: 无穷位 arch 补偿（PARTIAL/GAP-A）
```
def V2C3 (infDeficit : R) : Prop := infDeficit <= log (Real.sqrt 2 * Real.pi)
theorem v2c3_implies (h : V2C3 d) (hd : M = A - R = ... + d) : 0 <= M
```
来源：archDefect_nonneg（Gap.lean:463）；paper arch = log(sqrt 2*pi)。
GAP-A：`sum_i hullPacket_i(inf)` 与 `log(sqrt 2 pi)` 的等价**未证**（VcI.lean archDefect 项 vs paper archConstant），见 hull DECOMP-R-LOCAL §2。

### V2-C4: 分组（按 rational prime）正负预算（PARTIAL）
```
def V2C4 (p) : Prop :=
  qScalingPiece p <= tamePositive p + archShare p + ind2Buffer p
theorem v2c4_implies_M : (forall p, V2C4 p) -> 0 <= M   -- 需 arch 全局项的一次性归属
```
来源：tame（VcI:435）、archDefect（Gap:463）、ind2Term（Gap:756）。**注意**：ind2Term/gap 是 SSIneq gap 分解的项；只有证明它们确实进入 rhs 的 packetVol 展开（而非另行定义），才能进 M。未证 ⇒ GAP。

## 3. 禁止项（shehdd 审查意见落地）

1. **禁止移项重排**：M 只能按 §0 的 `M = A + (1/nC) sum P` 展开；不得把 R 的分项搬到左边或把 A 移到右边构造新不等式。
2. **禁止 buffer 当额外正项**：`(1-1/e)logp` 只在它确实出现在 packetVol/componentVol 展开中时可用；不能作为外部加项补 M。
3. **禁止恒等层冒充**：Theta scale 恒等式、c_lana 恒等式、paper 符号重写都不是正性证据。
4. **禁止假设目标**：不得假设 SSIneq、variant、PaperNormVerdict、`M >= 0`、`R <= A`、或 arch 等价作为候选的充分条件。
5. **禁止 gap 循环**：`gap >= 0`（Gap.lean:514）本身依赖 `logVol >= rhs`，其方向若用于 R 上界即循环；只有当 gap 项被证明是 M 展开的一部分且其正性来源独立（componentVol_le_leastHull 型）时才允许引用，且须显式检查依赖闭包。

## 4. 循环性自检（每候选的依赖闭包）

检查项：候选的证明项类型中不得出现 `Iut.Wall.SSIneq`、`PaperNormVerdict`、`Corollary312Variant`、`Var`、`M >= 0`、`R <= A`。

| 候选 | 允许依赖 | 禁用依赖 | 当前状态 |
|---|---|---|---|
| V2-C1 | ord/log、scaleElt、tame 展开 | SSIneq/variant/PaperNormVerdict | GAP（缩放归一化未证） |
| V2-C2 | packetWeight_pos、tame/arch/ind2 正性 | 同上 + gap 正性（除非确为 M 项） | PARTIAL（componentVol 负项未控） |
| V2-C3 | archDefect_nonneg | 同上 + H_inf = arch 未证 | GAP-A |
| V2-C4 | 同上组合 | 同上 + 不得把 ind2 当作 M 项（未证） | PARTIAL |

## 5. 结论

目标 v2 = `M = A - R >= 0`（A=|log q|/(2l)，R=|log Theta|）已按 packetVol 链显式展开；
M 中正项来源清晰（tame、archDefect、shellDefect、ind2Term 等，均 green-by-source），负项
唯一（q-scaling），但缩放常数归一化（`sum_j j^2` 与 `2l` 的系数关系）、arch 等价（GAP-A）、
ind2/gap 是否进入 M 展开（GAP-C）均未证。无候选可作为 M>=0 的证据；下一步是在
`Mzk1PaperNormThetaActual` 的符号层补齐 scaling 归一化恒等式后重试 V2-C1/V2-C2。
## A997 补：scaling 归一化恒等式与显式 M 改写

- 恒等式（Lean `Mzk1ScalingNormalizationActual.sum_jsq_eq_nC_mul_sFactor`）：
  `sum_{j=1}^{nC} j^2 = nC * sFactor nC`，`nC=(l-1)/2`；来源 `avgJSquare_eq_l`
  (Mzk1ProcessionAverageActual) + `sFactor` 定义 (Mzk1ShellArithmeticIdentitiesActual)。
- q-scaling 化归（`qScalingNeg_eq_neg_sF_mul_A`）：
  `-(1/(2l)) * sum_j j^2 * v_p(q) log p = - sF * A_p`，`A_p = v_p(q)log p/(2l)`。
- 显式 M：`M = (1/nC) sum_i sum_v sum_c packetWeight * componentVol_pos - (sF-1) * A`，
  其中 `componentVol_pos` 为去掉 q-scaling 后的非负项（tame shell/archDefect/
  shellDefect；ind2Term 是否进入 M 仍 GAP）。
- **剩余唯一不等式**：`(sF-1)*A <= qPositiveSum`（Lean `RemainingInequality`）；
  若成立则 `M >= 0`（`M_nonneg_of_remaining`，linarith）。
- 每项来源/符号：tame shell `>=0`（VcI.435）、archDefect `>=0`（Gap.463）、
  shellDefect `>=0`（Gap.442）、ind2Term `>=0`（Gap.756，入 M 未证）、
  orderVol `<=0`（VcI.102，负项）、packetWeight `>0`（LogVolume.153）。
- 状态：恒等式与化归为 **lean-written/uncompiled**；剩余不等式仍 OPEN，无候选成立。