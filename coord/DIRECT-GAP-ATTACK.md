# DIRECT-GAP-ATTACK — 直接计算 qThetaPilotLogVolumeComparison 的路线 + green 工具清单

生效日期：2026-11-11（A768，qpilot 起草）。目标：把 3.12 的唯一 remaining gap
`qThetaPilotLogVolumeComparison C3 P`（即 `paperGap`）化成**可直接计算**的两个实数的比较：
`qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3`。

结论先行：
- 两个读数**都有 green 定义与恒等式**（下面 §1），且都已接到 `paperGap`（green 桥，§1.4）。
- 缺的不是定义，而是**逐位分解/归一化字典**：把 `thetaPilotHullLogVolumeReal` 展开成
  `Σ_p (hull 半径项)·log p + arch`，把 `qPilotLogVolumeReading` 展开成 `−Σ ord_p(q) log p`。
  这两条展开所需的 lana 级引理（`hullPacket_finite`、`componentVol_leastHull_tensorLogShell_eq`）
  目前**没有本地 olean**（lana 源码已读，见 §3）。
- 6.1/6.3/6.4 的分析对应的 green 对象见 §4；6.3 的逐 capsule 反例在当前 C3 载体上**还不能表达**
  （载体是全局 tensor block，没有 capsule/procession 分解）。

---

## 1. Green 工具清单（文件 + 定理名）

### 1.1 q 侧：`qPilotLogVolumeReading`
文件 `tmp/sheaf/xif/paper/QPilotObjectActual.lean`（green olean）：
- `structure PaperQPilotObjectActual`（`line`、`strip`、`oneColumn`、`logKummer`、`oneZero`）；
- `PaperQPilotObjectActual.signedQPilotLogVolume := localSignedLog P.line.C3.q`；
- `signedQPilotLogVolume_eq_log_norm : signedQPilotLogVolume = Real.log ‖P.line.C3.q.q‖`；
- `signedQPilotLogVolume_neg : signedQPilotLogVolume < 0`；
- `qPilotLogMagnitude := −signedQPilotLogVolume`，`qPilotLogMagnitude_eq_localLogMagnitude`。

文件 `tmp/sheaf/xif/paper/QPilotScalarIdentificationActual.lean`（green）：
- `signedQPilotLogVolume_eq_paperQPilotLogVolume`；
- `signedQPilotLogVolume_eq_neg_abs_qParameter : signedQPilotLogVolume = −|log‖P.line.C3.q.q‖|`；
- `signedQPilotLogVolume_nonpos`。

文件 `tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean`（green）：
- `qPilotLogVolumeReading P := P.signedQPilotLogVolume`（def）；
- `qPilotLogVolumeReading_eq_neg_abs_qParameter`；
- `qPilotLogVolumeReading_nonpos`；
- `qThetaPilotLogVolumeComparison C3 P := qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3`（def）；
- `qThetaPilotLogVolumeComparison_iff`。

文件 `tmp/sheaf/xif/paper/S3137LogThetaLatticeLogShellReadyActual.lean`（green）：
- `precedingLogLink_q`、`precedingLogLink_scale`（q 值在 lattice 上的位置与尺度）；
- `thetaPilotPosition := (0,0)`、`qPilotPosition := (1,0)`、`logShellPosition := (0,1)`、
  `comparisonPosition := (1,1)`、`logShellReady` 等。

### 1.2 Θ 侧：`thetaPilotHullLogVolumeReal`
文件 `tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean`（green）：
- `thetaPilotHull C3 := actualHolomorphicHull C3 (actualUnitRegion C3)`（def）；
- `thetaPilotHull_eq_region : thetaPilotHull C3 = actualC3LogShellTensorRegion C3`；
- `thetaPilotHull_compact`；
- `thetaPilotHullLogVolume : ENNReal := haarLogVolume (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)`；
- `thetaPilotHullLogVolume_eq_regionLogVolume`；
- `thetaPilotHullLogVolume_ne_top`；
- `thetaPilotHullLogVolumeReal : ℝ := Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal`；
- `thetaPilotHullLogVolumeReal_eq_regionLogVolume`。

文件 `tmp/sheaf/xif/paper/C3LogShellTensorPacketActual.lean`（green）：
- `C3LogShellTensorBlock C3`（carrier，按 `C3.tensorIndex` 索引的有限维 ℚ_p 空间）；
- `actualC3LogShellTensorRegion C3` 与 `actualC3LogShellTensorRegion_compact`；
- `actualC3LogShellTensorIQ C3`（ℚ-span）；
- `actualC3LogShellTensorHaar C3 := Measure.addHaar`，instance `IsAddHaarMeasure`；
- `actualC3LogShellTensorLogVolume`；
- `structure ActualC3LogShellTensorPacket`（region/IQ/haar/logVolume 的打包，带 eq 字段）。

文件 `tmp/sheaf/xif/paper/C3LogShellTensorHolomorphicHullActual.lean`（green）：
- `HullBlock C3 := C3LogShellTensorBlock C3`；
- `actualUnitRegion`、`actualNonzeroScalings`、`actualScaledRegion`、`actualCandidateHulls`、
  `actualHolomorphicHull`；
- `actualRegion_subset_hull`、`actualHolomorphicHull_subset_candidate`、
  `actualUnitRegion_subset_hull`、`actualUnitRegion_mem_candidateHulls`、
  **`actualHolomorphicHull_unitRegion_eq`**（hull = region，S3137 用它证 `thetaPilotHull_eq_region`）、
  `actualHolomorphicHull_monotone`。

文件 `tmp/sheaf/xif/paper/S3137C3LogShellPacketNormalizedLogVolumeActual.lean`（green）：
- `c3TensorBlockDimension C3`、`c3TensorBlockDimension_pos`；
- `c3Tensor_measure_prime_smul`、`c3Tensor_log_measure_prime_smul`（p-缩放律，测度层面）；
- `c3PacketNormalizedLogVolume C3 μ S := Real.log (μ S).toReal / c3TensorBlockDimension C3`；
- **`c3PacketNormalizedLogVolume_prime_smul : ...(p • S) = −log p + ...`**（IUT III Prop 3.9(i) 的 packet 归一化）；
- `c3TensorRegion_measure_lt_top`；
- `c3TensorRegion_measure_prime_smul`、`c3TensorRegion_packetNormalizedLogVolume_prime_smul`。

其它可用 green（归一化/缩放）：
- `tmp/sheaf/xif/paper/PaperC3TensorHaarHullActual.lean`（tensor Haar/hull 接口）；
- `tmp/sheaf/xif/paper/Mzk1ThetaHullHaarNormalizationActual.lean`；
- `tmp/sheaf/xif/paper/S3137LogShellHaarLogVolumeScalingActual.lean`；
- `tmp/sheaf/xif/paper/S3137ThetaHullVolumeScalingActual.lean`；
- `tmp/sheaf/xif/paper/Mzk1ThetaHullScalingConsumerGlueActual.lean`；
- `tmp/sheaf/xif/paper/Mzk1HullLogVolumeFormulaActual.lean`；
- `tmp/sheaf/xif/paper/Mzk1SSIneqExplicitFormActual.lean`（`SSIneqExplicit`、σ-判据）；
- `tmp/sheaf/xif/paper/Mzk1KappaLemmaActual.lean`（κ-引理）；
- `tmp/sheaf/xif/paper/Mzk1ShellCoeffComputationActual.lean`（c_V = 1/4，σ* = 6）；
- `tmp/sheaf/xif/paper/Mzk1SSIneqNonemptyActual.lean`（R3：σ≤5 条件非空、σ=6 的 l≤12 充分条件、l>12 精确缺口）；
- `tmp/sheaf/xif/paper/Mzk1FinalBoundarySzpiroActual.lean`（Szpiro6Shape 及两方向条件定理）。

### 1.3 共享容器与 paperGap（green）
- `tmp/sheaf/xif/paper/Mzk1N3SharedContainerRealActual.lean`：
  `paperAnalyticSpace`、`paperHaarVolumeReading`、`paperHaarVolumeReading_thetaPilotHull`（rfl）、
  `SharedContainerReal`、`paperSharedContainerReal`、`paperGap`、`paperGap_paperSharedContainerReal`。
- `tmp/sheaf/xif/paper/Mzk1N3SharedContainerBridgeShaActual.lean`（shehdd，green）：
  `paperGap_iff_qThetaComparison`、`paperGap_iff_paper312Statement`、
  `paperSharedContainerReal_paperGap_iff`、`cor312_of_sharedPaperGap`。
- `tmp/sheaf/xif/paper/Mzk1SwitchAuditActual.lean`：两开关审计 + 空真修复
  （`SharedContainerGap` SUPERSEDED、`final_conditional_ABC.hfull` RETRACTED，
  替代陈述 `paperGapStatement := paperGap (paperSharedContainerReal C3 P)`）。

---

## 2. 直接计算路线（`qThetaPilotLogVolumeComparison`）

记 Q := `qPilotLogVolumeReading P`，H := `thetaPilotHullLogVolumeReal C3`。要证 Q ≤ H，按四步：

**Step A — Haar 归一化选择。** 我们取 `actualC3LogShellTensorHaar := Measure.addHaar`（green，
有 `IsAddHaarMeasure`）。这是**未按 maximal order 归一**的 choices；lana 的 `componentVol` 按
`(R_I)^~` 归一。两者相差每个素数一个常数（= log[(R_I)^~:R_I]/n 类型），在 `c3PacketNormalizedLogVolume`
（除以 `c3TensorBlockDimension`）里已经被吸收为 `−log p` 的 p-缩放（green 定理
`c3PacketNormalizedLogVolume_prime_smul`）。**这是当前最接近可算的归一化字典**：逐素数把
`paperHaarVolumeReading` 换成 `c3PacketNormalizedLogVolume`，差项显式记为 `O(Σ log p)`。

**Step B — log-shell 测度。** p-缩放律 `c3Tensor_log_measure_prime_smul` 给出
`μ(p·S) = p^{−dim}·μ(S)`（dim = `c3TensorBlockDimension`）；由此 `c3PacketNormalizedLogVolume_prime_smul`
给出每 packet 的 `−log p` 项。逐因子版本（lana `factorShellVol`、tame 的 `(1−1/e_j)log p`）需要
把 block 按 `C3.tensorIndex` 分解成因子坐标的乘积测度——**这是 Step B 的缺口**（见 §3）。

**Step C — tensor 测度积。** `C3LogShellTensorBlock` 是有限维 ℚ_p 空间上的 tensor；Haar 的乘法性
（Mathlib 的 product Haar / `Measure.addHaar` 的 product instance）应给出
`μ(⊗_j S_j) = ∏_j μ_j(S_j)`（在同一归一化下）。green 已有 dim 归一化与 prime-smul 律；
**一般乘积公式没有单独 green 引理**（需在 Step B 的因子分解后由 Mathlib product measure 直接给出）。

**Step D — q 的 ord 展开 + hull 半径。**
- q 侧：`signedQPilotLogVolume_eq_log_norm : Q = Real.log ‖q.q‖`，于是
  `Q = Σ_p v_p(q) log p`（用 `Real.log` 的乘积性 + q 的素因子分解；N1 模型 A703
  `CorrectedTripleThetaData` 取 q = (abc)²，v_p = 2v_p(abc)，这给出逐位显式展开）。
- Θ 侧：lana 的 `componentVol_leastHull_tensorLogShell_eq` 给 `H = Σ_j ρ_j log p`（ρ_j 为 log-shell 半径），
  tame 情形 `ρ_j = 1 − 1/e_j`（`componentVol_leastHull_tensorLogShell_eq_tame`）；这是**最关键的
  missing local lemma**（lana 已证，本地无 olean，见 §3）。
- 有了 D 的两侧展开，Q ≤ H 变成逐素数系数不等式；用 §1.2 的 `c_V = 1/4`/procession 平均
  就能回到 `Szpiro-6` 形状（`Mzk1FinalBoundarySzpiroActual` 与 `Mzk1ShellCoeffComputationActual`）。

**可直接写死的形式（无需新数学）**：`Q = −|log‖q.q‖|` 与 `H = log(μ(hull))`，因此
`Q ≤ H ⟺ μ(hull) ≥ exp(−|log‖q.q‖|)`；green 桥已把它与 `Paper312Statement` 等同。
真正的内容只在把 `μ(hull)` 算成 `(1/4)·l·(log d+log f)` 主项——见 §3 缺口。

---

## 3. lana 侧已读、本地未编译的关键引理（缺口清单）

- `Iut/WallEquiv/VcI.lean`（green 于 lana，本地无 olean）：
  - `hullPacket_finite : hullPacket = ∑_c w_c·∑_j ρ_{c j}·log p`（精确，所有素数）；
  - `componentVol_leastHull_tensorLogShell_eq : μ^log(hull(⊗𝓘)) = ∑_j ρ_j·log p`；
  - `componentVol_leastHull_tensorLogShell_eq_tame`（ρ_j = 1 − 1/e_j）；
  - `logVol_hull_vcI_eq`（procession 均匀平均 `/ℓ*`）；
  - `shellExcess_eq_tame`、`orderVol` 系列（packet index term）。
- `Iut/Concrete/ThetaRegion.lean`（green 于 lana，未 local）：`scaleEltAt`（指数 (i+1)²）、
  `thetaFiniteOn`、`thetaComponentOn`、`ivLabels`/`litLabels`。
- `Iut/Concrete/ArchScaling.lean`：`logVol` = (`∑_i packetVol`)/`nC` 的均匀平均。

**缺口结论**：本地可用的 green 只到「carrier + Haar + hull = region + p-缩放」层面；
逐素数 `ρ_j`、capsule/procession 分解、以及 archimedean 精确值（lana `VcI.md` 表格）
都不在本地 green 里。第一步应是把 lana 的 `VcI.lean`/`ThetaRegion.lean` 编译出 olean
（或把上面 5 条引理以 Mathlib-level 重证）。

---

## 4. 6.1 / 6.3 / 6.4 对应到 green 对象

| ROUTES 段 | 内容 | 可直接用的 green | 缺 |
|---|---|---|---|
| 6.1 | 数值检验台（`(1/6)log q ≤ (1+O(1/l))·[log f + ...]`） | `Mzk1SSIneqExplicitFormActual`（`SSIneqExplicit`、σ-判据）、`Mzk1SSIneqNonemptyActual`（σ≤5 非空、l>12 精确缺口）、`Mzk1FinalBoundarySzpiroActual`（`Szpiro6Shape` 双向条件定理） | 显式常数 C₀、`ω_{<l}` 的显式计算（无 green） |
| 6.2 | 精确壳形状猜想 | 无 green（纯纸面） | 全部 |
| 6.3 | 逐 capsule 包含式反例 | `pilot_lattice_positions`、`thetaPilotHull`、`actualUnitRegion`（green） | **capsule/procession 分解不在 C3 载体上**；lana `thetaComponentOn` 未本地编译；`ord_p(q)=2v_p(abc)` 的显式反例未形式化 |
| 6.4 | l 充分大时墙真 | `c_V = 1/4`（ShellCoeff，green）；`ℚ_l(ζ_l) ⊆ K_v` 数据接口在 OriginalInput（green 结构） | `l` 上方各位的贡献 `((l+5)/4)h_l log l`、`h_l` 下界、`log q` 上界（无 green） |
| 6.5 | 两开关审计 | `Mzk1SwitchAuditActual`（green，见文件） | — |

---

## 5. 建议最小路径（按投入产出排序）

1. **编译 lana `VcI.lean`/`ThetaRegion.lean`**（+ 依赖）得到 olean：立刻拿到 `hullPacket_finite`、
   `componentVol_leastHull_tensorLogShell_eq(_tame)`，Step D 的 Θ 侧展开即可完成。
2. 在 `C3LogShellTensorBlock` 上定义**因子投影**（按 `C3.tensorIndex`），把 `c3TensorBlockDimension`
   分解为各因子维数之积，用 Mathlib product Haar 得 Step C 的乘积公式。
3. 用 `c3PacketNormalizedLogVolume_prime_smul` 逐素数建立 `paperHaarVolumeReading` 与 lana
   `componentVol` 的归一化字典（差项 = per-prime `log[(R_I)^~:R_I]/n`），把 `qThetaPilotLogVolumeComparison`
   化为 `Σ_p ρ_p log p ≥ −|log q|` 的逐位不等式。
4. archimedean 项：green 只有 `componentVol_archLogShell_le_leastHull_le` 的上下界；
   精确值（lana `VcI.md` 表）需要新的测度计算（Euclidean ball vs polydisc，√N 相似比）。
5. 若 1–3 完成，最终边界的字典缺口就只剩「两套 log-volume 的逐位对齐」
   （见 `Mzk1FinalBoundarySzpiroActual.remainingDictionaryGaps`）。

---

## 6. 现状一句话

**两条读数都已 green 且已桥接到 `paperGap`；直接计算的卡点只剩 lana 级逐素数展开
（`hullPacket_finite`/`componentVol_leastHull_tensorLogShell_eq`）与 archimedean 精确值。**
