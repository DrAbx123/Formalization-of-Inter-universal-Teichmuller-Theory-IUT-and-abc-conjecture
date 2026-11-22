# Task M 调研备忘：Mathlib 测度/Haar/积测度/非局部紧群，与 RootThetaCarrier / product / skeleton

日期：2026-10-30。性质：只做调研，无新 Lean 证明、无 fake 对象、未改 TASK_LEDGER。
本 memo 回答：能否给 RootThetaCarrier / RootThetaProductCarrier / tensor-hull skeleton
上 actual Haar/log；能否处理 AlgebraicClosure product；列 theorem 名与适用性。

## 0. 结论（先看这个）

| 载体 | actual Haar | actual log | 结论 |
|---|---|---|---|
| 有限根扩张积 `(b : Bad) → rootNormedExtension T b`（L_b = K(root_b)） | 是（已有 actual） | 是（已有 actual normalized log） | 可直接用；Mathlib `Measure.addHaar` + `Measure.pi` + `Measure.pi.isAddHaarMeasure` |
| `RootThetaCarrier` / `RootThetaProductCarrier`（AlgebraicClosure 单位积） | **否** | **否 canonical** | 拒绝：AC 非局部紧，无 `LocallyCompactSpace`，`Measure.addHaar` 不能实例化；`pi.isAddHaarMeasure` 循环 |
| tensor-hull skeleton `RootThetaTensorHullCarrierGapAt`（tensorCarrier := RootThetaProductCarrier） | 否 | 否 | 其 `Minimal...Gap` 只是 norm bound（actual），不是 measure gap；不能补 Haar |
| root stack groupoid / section monoid（S356/S392） | 否（只有有限计数/Dirac） | 否 | 拒绝作 paper Haar log；quotient Haar 需要局部紧群，AC 不满足 |
| Berkovich skeleton | Mathlib 无 Berkovich（grep 0） | 无 | 拒绝；外部 Jonsson-Nicaise 是 asymptotic/model-dependent，无 exact bridge |
| AC product 的“可接受的 actual 替代” | 是（pushforward，非 Haar） | 是（相对 L-单位球的 log） | 沿闭嵌入 `L_b → AC_b` 推前 `rootExtensionProductHaar`；label 为 pushforward，不能称 Haar |

一句话：**Mathlib 只能用 actual Haar/log 于有限局部紧的 L 乘积；不能给 AC 乘积 actual Haar。
paper Θ-pilot hull log 的 exact gap 不是测度论工具能补的；AC Haar gap 是数学上不可填的（不是漏引理）。**

## 1. Mathlib 测度理论 / Haar / product measure 清单（本 checkout 实测）

Mathlib rev: `905b95818eb32af7874a58b427f50c1711a5e96c`（Lean 4.32.2，lake-manifest.json）。
以下名字均用 `lake env lean` 以 `#check` 实际验证过（见 tmp/m_haar_probe*.lean）。

### 1.1 局部紧 Haar（core）

| 名字 | 文件:行 | 精确假设/结论（实测） | 适用性 |
|---|---|---|---|
| `Measure.addHaar` | `Mathlib/MeasureTheory/Measure/Haar/Basic.lean:580`（`haar` 的 to_additive） | `[AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] : Measure G` | 只适用于局部紧；对 `rootNormedExtension` 可用，对 `AlgebraicClosure` 不可用 |
| `Measure.addHaarMeasure` | 同上 :517 | `(K₀ : PositiveCompacts G) : Measure G` | 归一化版本；L 上可用 |
| `Measure.isAddHaarMeasure_addHaarMeasure` | 同上 :570 | `(Measure.addHaarMeasure K₀).IsAddHaarMeasure` | 给 Haar 实例；L 上可用 |
| `Measure.IsAddHaarMeasure` | `Mathlib/MeasureTheory/Group/Measure.lean:762` | class，extends `IsFiniteMeasureOnCompacts`, `IsAddLeftInvariant`, `IsOpenPosMeasure`；**class 本身不含局部紧** | 可陈述，但构造仍需局部紧 |
| `Measure.IsAddHaarMeasure.smul` / `.nnreal_smul` | `Group/Measure.lean:787` / `:792` | 非零有限常数倍仍是 Haar | 归一化/缩放；S663 已在用 |
| `Measure.IsAddHaarMeasure.sigmaFinite` | `Group/Measure.lean:908` | `[SigmaCompactSpace G]` ⇒ `SigmaFinite μ` | L 是 σ-紧（第二可数+局部紧），product 的 `SigmaFinite` 由此来 |
| `Measure.addHaarMeasure_unique` | `Basic.lean:666`（`haarMeasure_unique`） | `[SecondCountableTopology G] (μ) [SigmaFinite μ] [IsAddLeftInvariant μ] (K₀) : μ = μ K₀ • addHaarMeasure K₀` | 比较 L 上两个 Haar；S255/S264 已在用 |
| `Measure.addHaarScalarFactor` | `Measure/Haar/Unique.lean:277`（`haarScalarFactor`） | `(μ' μ) [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ'] [μ'.IsAddLeftInvariant] : NNReal` | 比较两个 Haar 的标量；不需要局部紧 |
| `Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure` | `Haar/Unique.lean:646`（to_additive） | `[LocallyCompactSpace G] ... {s} (h's : IsCompact (closure s)) : μ' s = addHaarScalarFactor μ' μ • μ s` | 相对 log 的核心；`NormalizedHaarTransport` 在用 |

### 1.2 积测度（product measure）

| 名字 | 文件:行 | 精确假设/结论（实测） | 适用性 |
|---|---|---|---|
| `Measure.pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:210` | `[Fintype ι] [(i) → MeasurableSpace (α i)] (μ) : Measure ((i) → α i)`；**不需要拓扑/局部紧** | 可在任意 AC 乘积上定义“某族测度的积”；但没有 canonical 因子测度就无意义 |
| `Measure.pi_pi` | `Pi.lean:290` | `[∀ i, SigmaFinite (μ i)] (s) : (Measure.pi μ) (Set.univ.pi s) = ∏ i, μ i (s i)` | L 乘积单位球/盒测度；`PaperRootExtensionProductHaarActual` 已在用 |
| `Measure.pi.isAddHaarMeasure` | `Pi.lean:650`（`pi.isHaarMeasure` to_additive） | `[∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsAddHaarMeasure] [∀ i, MeasurableAdd] : (Measure.pi μ).IsAddHaarMeasure` | **L 乘积可用；AC 乘积不行（因子无 Haar）** |
| `Measure.pi_map_pi` | `Pi.lean:387` | `(hf : ∀ i, AEMeasurable (f i) (μ i)) : (Measure.pi μ).map (fun x i => f i (x i)) = Measure.pi (fun i => (μ i).map (f i))` | 逐因子推前；S304 已在用 |
| `Pi.locallyCompactSpace_of_finite` | `Mathlib/Topology/Compactness/LocallyCompact.lean:99` | `[∀ i, LocallyCompactSpace (X i)] [Finite ι] : LocallyCompactSpace ((i) → X i)` | 有限积局部紧；L 乘积可用，AC 乘积因子不满足 |
| `Topology.IsOpenEmbedding.locallyCompactSpace` | `LocallyCompact.lean:212` | `(hf : IsOpenEmbedding f) [LocallyCompactSpace Y] : LocallyCompactSpace X` | 开子空间继承局部紧；单位群从局部紧域继承 |
| `IsOpen.locallyCompactSpace` | `LocallyCompact.lean:224` | `(hs : IsOpen s) [LocallyCompactSpace X] : LocallyCompactSpace ↑s` | 同上；对 AC 因子不触发 |
| `IsOpenUnits` | `Mathlib/Topology/Algebra/IsOpenUnits.lean:40` | class；`isOpenEmbedding_unitsVal : IsOpenEmbedding (Units.val : Mˣ → M)`；域/group with zero 有实例 | 局部紧域 ⇒ 单位群局部紧；AC 不满足 |

### 1.3 推前 / 线性等价 / 球体积

| 名字 | 文件:行 | 适用性 |
|---|---|---|
| `ContinuousLinearEquiv.isAddHaarMeasure_map` | `Group/Measure.lean:890` | 沿连续线性等价推前 Haar；`RootTensorHaarIsometryActual`/`PaperRootTensorHaarLiftActual` 已在用 |
| `Measure.isAddHaarMeasure_map` | `Group/Measure.lean:813` | 需连续满射 proper 同态；本任务不必要 |
| `Measure.map_apply` | `Mathlib/MeasureTheory/Measure/Map.lean:160` | `(hf : Measurable f) (hs : MeasurableSet s) : (μ.map f) s = μ (f ⁻¹' s)`；推前计算 |
| `FiniteDimensional.proper` | `Mathlib/Analysis/Normed/Module/FiniteDimension.lean:543` | `[LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E] : ProperSpace E`；L=K(root) 有限维，项目已用 |
| `ProperSpace.isCompact_closedBall` | Mathlib（实测存在） | L 的闭球紧，测度有限 |
| `Metric.measure_ball_pos` | Mathlib（实测存在） | 需 `IsOpenPosMeasure`；L 的 Haar 有 |
| `Measure.addHaar_closedBall_mul` / `addHaar_real_closedBall'` | `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:460/479` | **只对 `NormedSpace ℝ E`**（实向量空间）；p-adic 不适用。p-adic 球体积用 `ProperSpace.isCompact_closedBall` + `Metric.measure_ball_pos`，项目已用 |
| `Measure.toSphere` | `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:51` | 只对实范数空间（`Module.finrank ℝ`）；p-adic 不适用 |
| `QuotientMeasureEqMeasurePreimage.haarMeasure_quotient` | `Mathlib/MeasureTheory/Measure/Haar/Quotient.lean:222` | 商 Haar，需 `[LocallyCompactSpace G]` + `[IsHaarMeasure ν]` + fundamental domain；AC 不满足 |

### 1.4 AlgebraicClosure / PadicComplex 的现状（关键）

| 名字 | 文件:行 | 事实 |
|---|---|---|
| `PadicAlgCl p` | `Mathlib/NumberTheory/Padics/Complex.lean:54` | `abbrev PadicAlgCl := AlgebraicClosure ℚ_[p]`，用 `spectralNorm.normedField` 给成 `NormedField` |
| `PadicComplex p` | `Complex.lean:137` | `abbrev PadicComplex := UniformSpace.Completion (PadicAlgCl p)` |
| `PadicComplex.isAlgClosed` | `Complex.lean:244` | `IsAlgClosed ℂ_[p]`；用 `IsAlgClosed.of_denseRange` + completion dense |
| `UniformSpace.Completion.denseRange_coe` | `Mathlib/Topology/UniformSpace/Completion.lean:325` | `DenseRange ((↑) : α → Completion α)` |
| `spectralNorm.completeSpace` | `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:936` | **只对 `[FiniteDimensional K L]` 给 `CompleteSpace L`**；完整 AC 不适用 |
| `spectralNorm.nontriviallyNormedField` | 同上 :870 | 给任意代数扩张 `NontriviallyNormedField`，**不给 CompleteSpace / LocallyCompactSpace / ProperSpace** |

实测（`#check`/instance probe，tmp/m_haar_probe3_20261030.lean）：
- `LocallyCompactSpace (PadicAlgCl 2)`：synthInstanceFailed
- `CompleteSpace (PadicAlgCl 2)`：synthInstanceFailed
- `ProperSpace (PadicAlgCl 2)`：synthInstanceFailed
- `LocallyCompactSpace (PadicComplex 2)`：synthInstanceFailed
- `ProperSpace (PadicComplex 2)`：synthInstanceFailed
- `LocallyCompactSpace (PadicAlgCl 2)ˣ`：synthInstanceFailed
- 连 `MeasurableSpace (PadicAlgCl 2)` 都不是 Mathlib 实例（项目应显式 `borel`）。

## 2. 为什么 AC 乘积不能有 Mathlib actual Haar（拒绝理由）

1. `Measure.addHaar` 的签名硬性要求 `[LocallyCompactSpace G]`；`PadicAlgCl` 与
   `AlgebraicClosure (NormalizedCompletion place)` 都没有这个实例，而且对 p-adic 情形在数学上是假的。
2. `Measure.pi.isAddHaarMeasure` 要求每个因子的 `(μ i).IsAddHaarMeasure`；AC 因子没有 Haar，
   所以是循环论证。`Measure.pi` 本身可以在任意可测空间上定义一族测度的积，但：
   - 没有 canonical 因子测度；
   - 得到的测度不是 Haar（不 translate-invariant）；
   - 没有 canonical 单位球归一化（正有限性只是额外假设）。
3. `IsHaarMeasure` class 虽不把局部紧写在字段里，但 Mathlib 的 canonical 构造与唯一性定理
   （`measure_isAddInvariant_eq_smul_of_isCompact_closure`, `haarMeasure_unique`）都要求
   `[LocallyCompactSpace]`；不存在“非局部紧群 Haar”的 Mathlib 构造。
4. 数学事实（未形式化）：`PadicAlgCl p` 稠密嵌入其真完成 `ℂ_[p]`（`denseRange_coe`），
   而 Hausdorff 群中的局部紧子群是闭子群；若 `PadicAlgCl p` 局部紧，则它在 `ℂ_[p]` 中闭且稠密，
   从而等于 `ℂ_[p]`，与 `PadicAlgCl` 可数、`ℂ_[p]` 不可数（或剩余域无限）矛盾。
   故“加一个 `LocallyCompactSpace (AlgebraicClosure)` 实例”不是补引理，而是引入假 axiom。
5. 项目现状与记录一致：
   - `PaperRootThetaProductCarrierActual` 明确写“There is no Haar measure on the full algebraic closure”；
   - `PaperRootThetaProductMeasureActual` 只有 finite Dirac image measure，并显式声明不是 Haar；
   - `PaperRootThetaProductHaarGapActual` 的 `RootThetaLocalHaarGapRequired` /
     `RootThetaProductHaarGapRequired` 是 exact gap，不能填；
   - `S647RootThetaExtensionHullMeasureActual.RootThetaExtensionHullMeasureRequired` 是 exact gap。
   这些 gap 与 Mathlib 的缺失完全对应，不能靠改类型/加实例“解决”。

## 3. LeanFormal 已有的 actual 工具（可直接复用）

### 3.1 有限根扩张 L_b（局部紧，Haar/log 都 actual）

文件：`tmp/sheaf/xif/paper/PaperRootExtensionHaarActual.lean`
- `rootExtensionProperSpace`（L_b 的 `ProperSpace`，由 `FiniteDimensional.proper`）
- `rootExtensionHaar : Measure (rootNormedExtension T b) := Measure.addHaar`
- `rootExtensionHaarIsAddHaar : Measure.IsAddHaarMeasure (rootExtensionHaar T b)`
- `rootExtensionUnitBall`, `rootExtensionUnitBall_measure_pos`, `rootExtensionUnitBall_measure_lt_top`
- `RootExtensionLocalHaarData`, `rootExtensionLocalHaarData`

文件：`tmp/sheaf/xif/paper/PaperRootExtensionProductHaarActual.lean`
- `RootExtensionProductCarrier := (b : Bad ...) → rootNormedExtension T b`
- `rootExtensionProductHaar := Measure.pi (fun b => rootExtensionHaar T b)`
- `rootExtensionProductUnitBall := Set.pi Set.univ (fun b => rootExtensionUnitBall T b)`
- `rootExtensionProductHaar_unitBall : ... = ∏ b, rootExtensionHaar T b (rootExtensionUnitBall T b)`（`Measure.pi_pi`）
- `rootExtensionProductHaar_unitBall_pos_lt_top`
- `rootExtensionProductNormalizedLog S := log μ(S) - log μ(unitBall)`
- `rootExtensionProductNormalizedLog_unitBall = 0`

文件：`tmp/sheaf/xif/paper/PaperRootExtensionThetaHullAuditActual.lean`
- `rootImageRadius`, `rootExtensionProductImageHull`
- `rootExtensionProductThetaImageSet_subset_imageHull`（actual containment）
- `rootExtensionProductImageHull_subset_unitBall`（在 `RootQUnitNormLeOne` 下）
- `rootExtensionProductImageHull_measure_pos_lt_top`（actual 正有限）
- `rootExtensionProductImageHullLog`（actual normalized log）+ `..._eq`

文件：`tmp/sheaf/xif/paper/PaperRootExtensionFieldScalingHaarActual.lean`
- `rootThetaFieldLambdaHaarFactor`
- `rootThetaFieldLambdaO_measure_eq_factor`（μ(λO)=factor·μ(O)）
- `rootExtensionProductFieldScaledHullLog`

### 3.2 completion/tensor block（局部紧，Haar/log actual）

- `PaperC3TensorHaarHullActual.lean`: `paperC3TensorHaar := Measure.addHaar`,
  `paperC3TensorHaar_isAddHaar`, `paperC3TensorHull_measure_pos_lt_top`,
  `paperC3TensorHullLogVolume`.
- `PaperLambdaOHullHaarActual.lean`: `paperLambdaOScaledRegion_measure_pos_lt_top`,
  `paperLambdaOCandidateLog`, `PaperLambdaOHullCandidateGap`（hull = single region 的 exact gap）.
- `PaperRootTensorHaarLiftActual.lean`: `rootTensorHaar`, `rootTensorHaarIsAddHaar`,
  `rootTensorUnitBall_measure = 1`, `rootTensorHaarLog = 0`.
- `RootTensorHaarIsometryActual.lean`: `blockHaar_map_eq_inv_smul_rootExtensionHaar`,
  `blockHaar_map_eq_rootNormedHaar`.
- `S255CommonHaarOnLActual.lean` / `S264CommonHaarScalarComputationActual.lean`:
  `commonHaarOnL`, `commonHaarScalarFactor`, `commonHaarOnL_eq_rootNormedHaar`.
- `S304QPilotTransportedHaarActual.lean`: `qPilotTransportedAmbientHaar_eq_pi_map`,
  `qPilotTransportedAmbientHaar_isAddHaar`（逐因子推前 + `Measure.pi.isAddHaarMeasure`）.
- `NormalizedHaarTransport.lean`: `measure_eq_haarScalarFactor_mul_image`,
  `relative_log_mass_image_eq`（拓扑加法群同构下的相对 log 不变；需两端 Haar + `[LocallyCompactSpace H]`）.
- `S663ActualAverageNormalizedHaarActual.lean`: `s663Measure`（任意平均的 normalized Haar）,
  `s663Measure_isAddHaar`, `s663Measure_unit_log`, `s663Interface`, `s663PaperSignedHull`.

### 3.3 AC 侧（只有 hull/carrier/有限像测度，没有 Haar）

- `PaperC3ThetaRootActual.lean`: `RootThetaCarrier := (v : V) → (RootExtension v)ˣ`
  （`RootExtension v = AlgebraicClosure (CommonPrimeCompletion ...)`）；`twoLthRootAt`,
  `paperRootThetaUnit`, `paperRootThetaUnit_pow_twoL`.
- `PaperRootExtensionEquivActual.lean`: `rootExtensionEquivUnits`（只是 identity ring equiv，
  不是到有限 L 的映射；L 是 AC 的 `IntermediateField`）。
- `RootThetaExtensionHullCarrierActual.lean`: `RootThetaExtensionCarrier := RootThetaCarrier`,
  `rootThetaExtensionImageSet`, `rootThetaExtensionHull`, `rootThetaExtensionImage_subset_hull`;
  `RootThetaToCompletionHullMapGap` 是 exact gap。
- `PaperRootThetaProductCarrierActual.lean`: `RootThetaProductCarrier`, `rootSupNorm`,
  `rootThetaUnitBall`, `rootThetaProductImagePoint`, `RootThetaRootNormBound`,
  `rootThetaProductImageSet_subset_unitBall`; `RootThetaProductMeasureGap` 是 exact gap。
- `PaperRootThetaProductMeasureActual.lean`: `rootThetaImageMeasure`（finite Dirac）,
  `rootThetaImageMeasure_unitBall = card(ThetaLabel)`（在 hq 下）,
  `rootThetaImageMeasure_unitBall_pos_lt_top`; 文件明说“不是 Haar”；`RootThetaProductHaarGap`.
- `PaperRootThetaProductHaarGapActual.lean`: `RootThetaLocalHaarData`（抽象 carrier + 局部紧 + addHaar）,
  `RootThetaProductHaarData`, `RootThetaLocalHaarGapRequired`, `RootThetaProductHaarGapRequired`;
  `rootThetaImageMeasure_eq_diracCount`.
- `S647RootThetaExtensionHullMeasureActual.lean`: `RootThetaExtensionHullMeasureData`
  （measurableSpace/measure/hullLogVolume/qParameterLogVolume/comparison 全为字段），
  `RootThetaExtensionHullMeasureRequired`; 没有 inhabitant。
- `S653RootThetaTensorHullCarrierGapActual.lean`: `rootThetaProductImageMap`（AC product → norm product）,
  `RootThetaTensorHullCarrierGapAt`（tensorCarrier/imageMap/imageSet/unitReference/lambdaHull）,
  `rootThetaTensorHullCarrierGapAtOfNormBound`（在 `RootThetaRootNormBound` 下）,
  `MinimalRootThetaTensorHullCarrierGap := RootThetaRootNormBound`。
  **这是 norm/carrier skeleton，不是 measure skeleton；补 norm bound 不产生 Haar。**
- `S356RootStackActionGroupoidActual.lean`: `RootObj`, `rootStackCategory`, `rootStackGroupoid`,
  `rootStackActionGroupoidData`; `RootStackMonoidSectionCarrier` exact gap。
- `S392RootStackSectionMonoidActual.lean`: `SectionCarrier := RootObj → Multiplicative ℤ`,
  `rootDelta`, `rootSectionCandidate`, `qSectionCandidate`, `rootStackMonoidSectionCarrier`.
  这只是离散函数模型；没有测度，也没有 paper O^▷。

### 3.4 p-adic log（是“log”，但不是 measure/log-volume）

- `LeanFormal/IUT/Foundations/LocalFields/AlgebraicUnitLogarithm.lean`:
  `isometry_intermediateField_inclusion`, `algebraicUnitLog`, `algebraicUnitLog_eq_map`,
  `algebraicUnitLog_eq_log1p`, `algebraicUnitLog_eq_zero_iff_isOfFinOrder`.
- `IntegralUnitPerfectionTopology.lean`: `unitPerfectionTopology`, `unitLogPerfectionEquiv`,
  `unitLogPerfectionHomeomorph`.
- `AlgebraicUnitPerfectionIndTopology.lean`: `algebraicUnitPerfectionIndTopology`,
  `algebraicUnitPerfectionIndHomeomorph`（ind/final topology 到加法 Ω 的同胚）.
- `UnitPerfectionFunctoriality.lean`: `unitPerfectionMap`, `unitPerfectionMap_log_commute`.

**适用性边界**：`algebraicUnitLog` 定义在 `(Integers Ω)ˣ`（norm = 1 的整单位）上；
q / q[2u] 的 norm < 1，不是 `Integers Ω` 的单位，故不能直接给 q[2u] 的 log。
更重要的是：这是 p-adic 群同态 log，不是 paper 的 Haar log-volume；不能替换
`qPilotLogVolume` / `paperRootThetaHullLog` / `signedHullLogVolume`。
注意 `sourceQPilotSignedLog` 实际是 `-∑ |Real.log (qParameter b)|`，
不是 p-adic `unitLog`（`tmp/sheaf/xif/PaperQPilotObject.lean:66-74`）。

## 4. 如果一定要在 AC product 上有“actual measure/log”：唯一诚实的推前路线

这不是 Haar，但可构造 actual measure，并且 log 与 L 乘积的 actual log 完全相同：

1. `L_b = rootNormedExtension T b` 是 `rootNormedAmbient T b = AlgebraicClosure (rootBase T b)`
   的 `IntermediateField`；inclusion `ι_b : L_b → AC_b` 是等距
   （`isometry_intermediateField_inclusion`，LeanFormal）。
2. `L_b` 有限维、完备，故 `ι_b` 是闭嵌入（`Isometry.isClosedEmbedding`，源头完备；
   或 `CompleteSpace` + 有限维）。
3. 定义 `ν_b := (rootExtensionHaar T b).map ι_b`（`Measure.map`；`Measure.map_apply` 计算）。
   `ν_b` 是 AC_b 上的 actual 测度（总质量无限），但**不是 Haar**：平移一个 `AC_b  L_b` 的元素
   会把支撑移出 `L_b`，不具平移不变性。
4. 在 AC 乘积上 `ν := Measure.pi (fun b => ν_b)`（`Measure.pi` 不需要局部紧）。
   `Measure.pi_pi` 可计算盒测度（若每因子 σ-有限）。
5. 对 L 乘积的 hull `H = Set.pi univ (fun b => closedBall 0 (r_b))`，
   `ι '' H` 在 AC 乘积中闭；用 `Measure.map_apply` + `ι` 单射得
   `ν (ι '' H) = rootExtensionProductHaar T H`；同理单位球；
   因此 `log ν(ι '' H) - log ν(ι '' B) = rootExtensionProductNormalizedLog T H`。
6. **诚实标注**：这是 “pushforward of the actual L-Haar”，不是 “Haar on the AC product”；
   它依赖 L 的选择，且不解决 paper hull equality（`PaperRootHullFormulaGap` /
   `PaperLambdaOHullCandidateGap` / `RootThetaToCompletionHullMapGap`）。
   如果只是为了给 `RootThetaCarrier` 一个 actual measure/log 以做外层接口，
   这是可用的；如果要宣称 paper Θ-pilot hull log，仍缺 hull equality。

## 5. 对 exact gap / Cor 3.12 的直接回答

- **能直接用于 exact gap 的 Mathlib 定理**：
  - 仅 `Measure.addHaar` + `Measure.pi` + `Measure.pi_pi` + `Measure.pi.isAddHaarMeasure` +
    `Measure.addHaarMeasure_unique` / `Measure.addHaarScalarFactor` +
    `Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure` 用于 **有限 L 乘积**；
    这些已经被项目用完（PaperRootExtension*），不产生新的 paper bridge。
- **不能直接用于 exact gap 的**：
  - 任何在 `RootThetaCarrier` / `RootThetaProductCarrier` 上的 actual Haar：无
    `LocallyCompactSpace`，且 `IsHaarMeasure` 的因子条件是循环。
  - tensor-hull skeleton 的 `unitReference/lambdaHull`：`S653` 的 `tensorCarrier` 就是
    `RootThetaProductCarrier`，其 `Minimal...Gap` 只是 norm bound；norm bound 不能替代 measure。
  - root stack groupoid/section monoid：无测度、无 paper O^▷；quotient Haar 不适用。
  - Berkovich skeleton：Mathlib 无 Berkovich（0 命中）；有限扩张 L 的 Berkovich 空间是单点；
    外部 skeleton measure 是 model-dependent/asymptotic，无 exact equality。
- **exact gap 仍然是**：
  - `RootThetaProductHaarGapRequired`（AC Haar）——无 Mathlib 解，数学上不可填；
  - `RootThetaExtensionHullMeasureRequired`（S647）——同上；
  - `PaperRootHullFormulaGap` / paper hull equality（不是测度论问题）；
  - `RootThetaToCompletionHullMapGap` / `PaperLambdaOHullCandidateGap`。
  结论：Task M 不能关闭 Cor 3.12 的 exact gap；只能确认“有限 L 乘积的 actual Haar/log 已到位，
  AC 乘积 Haar 必须拒绝，若需 AC 载体只能走 pushforward”。

## 6. 核查方式 / 未做的事

- Mathlib 名字用 `lake env lean` 实测 `#check`（tmp/m_haar_probe_20261030.lean,
  tmp/m_haar_probe2_20261030.lean）；AC/PadicComplex 实例缺失用 expected-failure probe
  （tmp/m_haar_probe3_20261030.lean）确认。
- 未重编译 LeanFormal/xif 的已有 actual 文件；其状态引用 `TASK_LEDGER.md` 的 ACTUAL 记录
  （未独立验证 integration/build）。
- 未改任何现有 Lean 文件、未改 TASK_LEDGER；本 memo 只新增调研记录。
- 外部文献：locally compact group 有 Haar measure（arXiv 2407.09742, ar5iv）；
  `Q_p^a` 非局部紧（Barria-Shamseddine, 2018）；非局部紧群无标准 Haar 构造。
  Berkovich/Jonsson-Nicaise 见 S728 memo 及其引用。

## 7. 给 lead 的一句话

**不要把 AC product 当 Haar 载体**：`Measure.addHaar` 需要 `LocallyCompactSpace`，
`PadicAlgCl`/`ℂ_[p]` 都没有且数学上不该有；`Measure.pi` 只能造“积测度”，不能造 Haar。
paper Θ-pilot hull log 的 actual 测度论部分已经由有限 L 乘积完成；
剩余 exact gap 是 paper hull equality / q[2u] root-stack bridge，不是 Mathlib 缺失。