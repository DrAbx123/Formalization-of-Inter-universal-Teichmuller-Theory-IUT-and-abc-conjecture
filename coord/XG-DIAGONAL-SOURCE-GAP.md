# XG-DIAGONAL-SOURCE-GAP — X_G 商与 diagonal 商等价的实际构造缺口

日期：2026-11-13（Asia/Shanghai）。只读分析 + 文档；未新增 Lean 文件（构造未完成，按纪律写精确缺口）。

## 1. 已 green 的组件

| 组件 | 文件/声明 | 用途 |
|---|---|---|
| X_G 列配对 | Mzk1DualTransposeActual.mem_padicIntegralTraceDualLattice_span_range_iff | x∈(span_Zp(range v))^# ↔ ∀i, B x (v i)∈Z_p（X_G=(G·Z_p^r)^#） |
| 左伴随 comap | Mzk1DualTransposeActual.padicIntegralTraceDualLattice_map_eq_comap | (eL)^#=(L^#).comap e.leftAdjoint |
| 对偶基 span | IntegralTraceDualLattice.padicIntegralTraceDualLattice_span_basis | (basisIntegralLattice b)^# = span_Zp (B.dualBasis hB b) |
| diagonal index | Mzk1DiagonalIndexActual.natCard_quotient_diagLatticeSubmodule | Nat.card((d→Z_p)⧸∏p^{e_i})=∏p^{e_i} |
| 条件体积桥 | Mzk1DualIndexLinkActual.dual_volume_ratio_of_quotient_cardinality | 给定 hq 得 μX/μL=(∏p^{e_i})⁻¹ |
| 商来源条件版 | Mzk1DualIndexSourceActual.XG_volume_ratio_of_quotient_equiv | 给定 φ : L⧸XG ≃+ diagonal 商 得体积比 |

## 2. 要构造的对象

目标：对实际 XG（Mzk1DualIntersectionActual.XG = LambdaG 的 trace dual）与 compact-open L，构造

φ : (L ⧸ XG.comap L.subtype) ≃+ ((d → Z_p) ⧸ diagLatticeSubmodule e)。

## 3. 精确缺口链

1. 把 L 写成 basisIntegralLattice：需一个实际 Z_p-基 b : Basis d Z_p L 与 L = basisIntegralLattice (b : Basis d Q_p M) 的等式（L 已有 Module.Free/Module.Finite，但“所选基与 L 的相等”未登记；arithmeticTupleValuationIntegerQpBasis 只对整块，不对任意 L）。
2. XG 与对偶基 span 对齐：需 XG = span_Zp (Set.range (B.dualBasis hB b))。可由 padicIntegralTraceDualLattice_span_basis 得到，前提是 (a) L = basisIntegralLattice b；(b) XG 被识别为 padicIntegralTraceDualLattice B L（Mzk1DualIntersectionActual.XG 定义是 LambdaG 的 dual，需要 LambdaG = L 的等式）。
3. SNF/对偶基系数识别（核心缺口）：需把 B.dualBasis hB b 写成 fun i => ∑ j, c_{i j} • b j，并证明其系数矩阵在 GL_d(Z_p) 下等价于 diag(p^{e_i})（Smith 标准形对偶步骤：对偶基系数 = 原初等因子的逆）。这正是 Mzk1TensorDualCorrectionActual 已标注的 GAP-DUAL-SNF（b7_card_eq_of_equiv 只把商等价作为显式输入）。
4. 由基/SNF 构造商等价：给定基 b、b' = B.dualBasis hB b 与 SNF 对角形，用自由模坐标构造 (L ⧸ XG) ≃+ ((d→Z_p) ⧸ ∏ p^{e_i})；现有 PadicLatticeIndexFormula 的 natCard_quotient_span_padicInt_pow 只给 rank-one/一个坐标的基数，没有整块商等价。
5. Haar 前提：μ XG 正/有限来自 XG compact open（Mzk1DualIntersectionActual.XG 的 compact/open 未证明；需 LambdaG compact open + trace dual 的 compact/open 定理，IntegralTraceDualLattice 目前只给 basis-lattice 的 finite/free，未给任意 compact-open 的 dual compact-open）。

## 4. 最小可交付顺序（若要继续）

A. 先对 basisIntegralLattice b 情形构造：XG := padicIntegralTraceDualLattice B (basisIntegralLattice b)；用 padicIntegralTraceDualLattice_span_basis 得 XG = span_Zp (range (B.dualBasis hB b))（已有）。
B. 在 d 有限坐标上，若 B.dualBasis hB b = fun i => (p^{e_i}) • b i（对角/置换型），则直接构造 L⧸XG ≃ (d→Z_p)⧸∏p^{e_i}Z_p：坐标 b 下 quotient 由坐标模 p^{e_i} 给出；可望用 Submodule.quotientPi + LinearEquiv 完成。
C. 一般 B.dualBasis 需 SNF：把 B.dualBasis hB b 的系数矩阵做 Smith 标准形，得到 U diag(p^{e_i}) V；这是 GAP-DUAL-SNF，需矩阵 SNF API + 有限自由模坐标。
D. 最后接 Mzk1DualIndexSourceActual.XG_volume_ratio_of_quotient_equiv。

## 5. 判定

- 当前不能构造完整 φ：缺 basis/LambdaG 等式、SNF 对偶步骤、XG compact-open 前提（第 3 条是硬核心）。
- 可先做 B 的对角/置换情形作为最小 green 子结果；一般情形保持 GAP-DUAL-SNF。
- 不新增假设换 green；不在 Lean 中用 sorry/axiom/占位等价。

## 6. 按 B（对角/置换情形）尝试记录（2026-11-13）

- 目标坐标模型：`M = d → ℚ_[p]`，`small = ∏ ℤ_[p]`，`large = ∏ p^{-e_i} ℤ_[p]`，`small ≤ large`；若构造 `large ⧸ small ≃+ (d→ℤ_[p]) ⧸ ∏ p^{e_i}`，则套 `Mzk1DualIndexLinkActual` 得 `μ(small)/μ(large) = (∏ p^{e_i})⁻¹`。
- 该坐标商映射应为 `x ↦ (p^{e_i} x_i mod p^{e_i})`：核 = `small`，满射到 diagonal 商；这是“逐坐标”构造，数学上直接。
- **未写成 Lean**：需要先定义 `large` 为 `Submodule.pi` 上的 `p^{-e_i}ℤ_[p]`（`zpow`/`inv` 幂），并证 `small ≤ large`、核/满射/商等价（`QuotientAddGroup.quotientKerEquivOfSurjective` 模式）；本轮时间/上下文不足，未硬凑。
- 列配对 (1) 的取向注意：在标准 trace pairing 下 `(diag(p^{e_i})ℤ_[p]^d)^# = ∏ p^{-e_i}ℤ_[p]`；若同时要求 `XG ⊆ L` 且 `L/XG` 的基数为 `∏p^{e_i}`，需把 `L` 取为 `∏ p^{-e_i}ℤ_[p]`、`XG` 取为 `∏ℤ_[p]`（否则 A2 方向/体积比为 `∏p^{e_i}` 而非逆）。因此 B 的 Lean 文件应明确这一取向，不能混用。
- 下一步（若继续）：写 `Mzk1DiagonalDualActual.lean`（坐标 large/small + 商等价 + 体积比），置换情形用排列矩阵复合；一般 SNF 保持 GAP-DUAL-SNF。

## 7. 符号取向更正（2026-11-13，按 Lead 更正）

- 标准 trace pairing 下 `(diag(p^{e_i})·Z_p^d)^# = ∏ p^{-e_i}Z_p`。
- 若 `e_i ≥ 0`：`p^{-e_i}Z_p ⊇ Z_p`，故 `XG ⊇ L=Z_p^d`，不能取 `XG ≤ L`；此时要么用 `μ(L)=index·μ(XG)` 的倒数形式，要么交换 large/small。
- 若 `e_i ≤ 0`：`p^{-e_i}Z_p ⊆ Z_p`，`XG ⊆ L`，`[L:XG]=∏ p^{-e_i}`，`μ(XG)/μ(L)=(∏p^{-e_i})^{-1}`。
- **本线采用 (iii) 的 `f_i := -e_i ≥ 0` 参数化**：`XG(f)=∏ p^{f_i}Z_p ⊆ Z_p^d = L`，`index=∏ p^{f_i}`，`μ(XG)/μ(L)=(∏p^{f_i})^{-1}`。新文件 `Mzk1DiagonalDualActual.lean` 用该取向（`coordSmall=L`、`coordDual(f)=XG`）；e 与 f 的符号约定固定为 `f = -e`，不再混用。
- 商等价 `L⧸XG(f) ≃ (d→Z_p)⧸∏p^{f_i}` 仍作为显式输入 `φ`（构造为 GAP）；文件只提供 f-参数化的条件包装，不声称构造。

## 8. 更新（23:45Z）：φ 链与 SNF 工具 green

- **`Mzk1DiagEquivProvedActual`**：DONE 23:23:45（37s）——`embLinear`、`embLinear_map_coordDualInt`（map=coordDual）、`integerProductEquiv : (d→Z_p) ≃ₗ coordSmall`。
- **`Mzk1DiagQuotCardActual`**：DONE 23:25:39（50s）——`integerProductEquiv_map_comap`、`diagQuotEquiv`、`natCard_quotient_coordSmall = ∏p^{f_i}`。
- **`Mzk1DiagVolumeProvedActual`**：DONE 23:45:39（75s），olean YES——`natCard_addSubgroup_quot` 用 `change` 桥到 Submodule 商；`diagonal_volume_ratio_actual` 直接把 cardinal 作为 `hq` 传入 `dual_volume_ratio_of_quotient_cardinality`，得 `μ(XG)/μL = (∏p^{f_i})⁻¹`（条件为 `XG≤L` 紧开与 μX 正有限；无 AddSubgroup/Submodule 商等价构造）。
- **`Mzk1SNFToolActual`**：DONE 23:33:54（28s）——`exists_smith_normal_form`（Mathlib `Submodule.smithNormalForm` wrapper；不移植）。
- **`Mzk1BasisDetUnitActual`**：DONE 23:43:22——`basis_change_det_isUnit : IsUnit (b.det b')`。
- **`Mzk1SNFDiagActual`**：DONE 23:43:23——SNF 对角数据 wrapper。
- **`Mzk1SNFDiagEquivActual`**：DONE 23:45:02（38s）——`snf_eq_span_diag : N = span_R (range (a_i • bM (f i)))`（`map_subtype_top` + `bN.span_eq` + `map_span`）。
- **`Mzk1GLActActual`**：DONE 23:45:08（44s）——`glAct_mem_coordSmall`：GL_d(Z_p) 矩阵作用保 `∏Z_p` 坐标格。
- **`Mzk1FactorPermutationLatticeActual`**：marker green（23:17:53）；subset 版内容见本文件前文。

## 9. GAP 状态

- GAP-DUAL-SNF 的**工具**已关闭（Mathlib SNF，无需移植）；一般 X_G 的 GL_d(Z_p)-等价仍需把 `snf_eq_span_diag` 与 `glAct_mem_coordSmall`/`basis_change_det_isUnit` 组合成一条定理（下一步）。
- Ind1→p-adic 整数格桥：仅正向 subset（FactorPermutation marker），反向/整数格等式 GAP。
- φ 非条件体积比：`Mzk1DiagVolumeProvedActual.diagonal_volume_ratio_actual` 已 green（仍以紧开/μ 正有限为条件）；无 AddSubgroup 商构造。
- 一般 SNF 商 cardinal：需 SNF 对角基底 + 商 cardinal；当前仅具体 diagonal 情形 green。

## 10. 下一步

1. 写 `xg_gl_diag_equiv`：把 SNF span 与 GL 保格/换基 det unit 组合为一般 X_G 的 GL_d(Z_p)-等价；
2. 把 `diagonal_volume_ratio_actual` 与 X_G 定义（LambdaG trace dual）接起来，替换条件 hle/紧开为实际构造；
3. 更新 ROUTE1/2 文档；Ind1 桥 reverse 仍 GAP（tprod 原像）。

## 11. 更新（11:01Z）：一般 SNF 体积比（条件版）green

- **`Mzk1GeneralSNFVolume3Actual`**：DONE 11:01:35（56s）——`general_snf_volume_ratio`：
  一般 `N ⊆ M`、SNF `(bN i : M) = a_i • bM i`、紧开/正有限 ⇒
  `μ(N)/μ(M) = (∏ p^{v_p(a_i)})⁻¹ = ∏|a_i|_p`。
  证明：`natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm`（商 cardinal）+ A2 桥 `latticeIndex_toAddSubgroup_eq_natCard_quotient` + `haar_measure_eq_index_mul_of_le` + ENNReal.toReal 代数化。
  `hle` 由 `change (N.map M.subtype).toAddSubmonoid ≤ M.toAddSubmonoid` + `exact hle_sub` 推导（不再作为假设）。
- **`Mzk1SNFMatrixDiagActual`**：DONE 10:53:16——`toMatrix_subtype_eq_diagonal`、`u_mul_diag_mul_w`（U=W=1 形式）。
- **`Mzk1SNFMatrixUWActual`**（待重编）：`u_mul_diag_mul_w_standard = U * diag a * W = toMatrix 标准基`（root namespace `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`），U/W det unit。

### 当前 GAP
- U/W 真换基文件待 watchdog；
- Ind1 反向（FactorPermutation subset 反向）；
- 一般 X_G（LambdaG trace dual）到 SNF 对角识别；
- canonical Haar（coordinateCompacts）消紧开假设。

## 12. 更新（11:06Z）：U/W 换基矩阵 green

- **`Mzk1SNFMatrixUWActual`**：DONE 11:06:43（22s）——
  `u_mul_diag_mul_w_standard`：`b.toMatrix bM * Matrix.diagonal a * bN.toMatrix bN0 = LinearMap.toMatrix bN0 b N.subtype`
  （root namespace `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`；U=`b.toMatrix bM`，W=`bN.toMatrix bN0`）；
  `u_det_isUnit` / `w_det_isUnit`：U/W det 为 ℤ_p 单位（复用 ChangeMatrix det unit）。
- **`Mzk1SNFMatrixDiagActual`**（10:53:16）：`toMatrix_subtype_eq_diagonal`、`u_mul_diag_mul_w`。
- **`Mzk1GeneralSNFVolume3Actual`**（11:01:35）：一般 SNF 体积比条件版 `μ(N)/μ(M)=(∏p^{v_p(a_i)})⁻¹`。

### 当前剩余 GAP
1. canonical 无条件化：把 `hMc/hMo/hNc/hNo/hNpos/hNtop` 用 `coordinateCompacts`（紧开、mass=1）与 `isCompact/IsOpen/measure_pos/measure_lt_top` 消去；
2. Ind1 反向（FactorPermutation subset 反向）；
3. 一般 X_G（LambdaG trace dual）到 SNF 对角识别；
4. GL 作用与体积比拼成 `μ(GL 轨道)/μ(L)` 的最终等式。

### 可复用 green 基座
- A2 桥：`Mzk1IndexCardBridgeActual.latticeIndex_toAddSubgroup_eq_natCard_quotient`；
- 商 cardinal：`PadicLatticeIndexFormula.natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm`；
- 对角矩阵：`Mzk1SNFMatrixDiagActual.toMatrix_subtype_eq_diagonal`；
- 换基矩阵：`Mzk1SNFMatrixUWActual.u_mul_diag_mul_w_standard` / `u_det_isUnit` / `w_det_isUnit`；
- canonical Haar：`Mzk1CanonicalHaarCoordLatticeActual.coordinateCompacts`/`coordinateCompacts_mass`/`canonical_map_eq_of_image_eq_full`。

## 13. 更新（12:20Z）：B4 canonical 与 #7 THETA-DEG

- **B4 canonical**：`Mzk1CanonicalDiagUncondActual` DONE 12:20:05Z，收口为 `canonical_diag_volume_ratio_compact_open`（条件 hLc/hLo/hXc/hXo；hXpos/hXtop 已由 IsOpenPosMeasure/measure_lt_top 推出）；`diagHomeo f '' coordSmall = coordDual` 的 **image bridge + compact/open 像为精确 GAP**（见 `Mzk1DiagEquivBridgeActual`）。
- **#7 THETA-DEG**：`Mzk1P7ThetaDegActual` DONE 12:20:07Z——`localCompletionDegree := Module.finrank ℚ_[p] (CommonPrimeCompletion place)`，`c3TensorBlockDimension = ∏ localCompletionDegree`。
- **B2**：`Mzk1P7ThetaDegB2Actual` **DONE 12:54:15Z**——域分解 `Block ≃ₐ ∏ E_j` ⇒ `finrank block = ∑ finrank E_j`；packet = Σ_tuple Σ_j。**C3 特化** `Mzk1P7ThetaDegC3Actual` **DONE 12:33:19Z**：`c3TensorBlockDimension = Σ 实际 local degree`。
- 依赖修复：`Mzk1C3BlockMeasureActual` DONE 11:44:02Z（`Nat.cast_pos` 取代 `exact_mod_cast`）。

## 14. 更新（13:39Z）：#7 THETA-DEG 全收口

- **#7 DONE**（4 文件证据）：`Mzk1P7ThetaDegActual`（localCompletionDegree=finrank，block 乘积识别）、`Mzk1P7ThetaDegB2Actual`（域分解 ⇒ finrank 求和 + packet 求和）、`Mzk1P7ThetaDegC3Actual`（C3 block:Q_p=Σ 实际 local degree）、`Mzk1P7ThetaDegWeightActual`（theta 权重=-(Σdeg)·log p，normalized 分母=Σdeg；p-scaling 引用既有 green）、`Mzk1P7ThetaDegCancelActual`（normalized=(1/Σdeg)·log(μS)；(1/Σdeg)·thetaPilotHullLogVolumeReal）。
- **B4 DONE（14:44:03Z）**：`Mzk1CanonicalDiagUncondFinalActual`（olean 216,480B）——**无条件** `canonical_diag_volume_ratio_uncond`；hle/hLc/hLo/hXc/hXo 全部由 coordinate/fractional lattice 紧开性构造，**绕开 diagHomeo image bridge**。旧 `Mzk1DiagEquivBridgeActual` 仅作历史记录，不再作为 GAP。
- 其他 green：A2 桥、U/W 矩阵、一般 SNF 体积条件版、DiagVolume、SNF 工具/DetUnit/Diag/GLAct。
