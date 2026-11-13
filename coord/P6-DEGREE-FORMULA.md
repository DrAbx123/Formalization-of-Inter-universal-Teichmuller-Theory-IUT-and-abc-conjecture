# P6-DEGREE-FORMULA — (C20) product formula & Arakelov degree 接口（R29m / task-93）

| field | value |
|---|---|
| Status | **task-93 completed / green**：复用 Example36 的数域 product formula；最小 Arakelov degree 接口 + 可加性/principal-unit 消失/degree 差公式 已 DONE EXIT=0；**Example36 degree ↔ 我们 S2717/S2807 log-volume 的桥未构造**（GAP-DEGREE-BRIDGE） |
| Lean | `tmp/sheaf/xif/paper/Mzk1ProductFormulaDegreeActual.lean`：**watchdog DONE EXIT=0**（`watchdog.log` 20:33:49Z，59s；olean 见下） |
| 纪律 | 无 sorry/axiom；接口是定义，一致性定理与接口分开；未新增假设；未把定义当定理 |

## 1. 盘点：已有覆盖（file:line）

### 1.1 `LeanFormal/IUT/IUTII/Frobenioid/Example36ProductFormula.lean`（445 行，**olean=True**）

| 内容 | 行 |
|---|---|
| `finitePlaceResidueCardinality_eq_absNorm`（#(O_F/v) = Ideal.absNorm） | :103 |
| `finitePlace_mk_apply_eq_residueCardinality_zpow`（|f|_v = #^−ν） | :110 |
| `finitePlace_log_mk_apply` | :125 |
| `infinitePlace_mult_eq_one_or_two`（[F_w:ℝ] = 1/2） | :135 |
| `finprod_finitePlace_eq_supportProd` | :162 |
| **`productFormula_log`**（Mathlib 乘积公式取 log 的严格形式） | :178 |
| **`log_finprod_finitePlace_eq_neg_weighted`** | :221 |
| **`productFormula_finsupp`**（规范化有限/arch 权重和 = 0） | :246 |
| **`weightedFiniteSum_eq_archimedeanLogSum`**（等权形式） | :271 |
| `productFormula_support` | :282 |
| **`globalPrimeStripWeight`**（显式除子上的 signed place-index 聚合） | :313 |
| **`globalPrimeStripWeightHom : ExplicitDivisor F →+ ℝ`** | :327 |
| `globalPrimeStripDegree`（乘法编码上的度） | :341 |
| `globalPrimeStripDegreeKernel`（FrobenioidValueKernel） | :362 |
| **`globalPrimeStripWeight_principalDivisorExplicit`**（principal unit 上度为 0） | :387 |
| `globalPrimeStripDegreeKernel_realification_principalUnit` | :399 |
| `globalPrimeStripDegreeKernel_degree_principalUnit` | :408 |
| `globalPrimeStripWeight_globalModelDivisor`（backend 形式） | :424 |
| `globalPrimeStripWeight_sourceModelInput_divisor` | :435 |

### 1.2 Mathlib `NumberTheory/NumberField/ProductFormula.lean`（green）

| 内容 | 行 |
|---|---|
| `FinitePlace.prod_eq_inv_abs_norm_int` | :45 |
| `FinitePlace.prod_eq_inv_abs_norm` | :77 |
| **`prod_abs_eq_one`**（数域局部绝对值乘积 = 1） | :98 |

### 1.3 局部 log-volume / det 簿记（green）

| 内容 | 位置 |
|---|---|
| `haarLogVolume` / `haarLogVolume_of_lt_top` / `haarLogVolume_mono` | `Mathlib`-side? 实际在 `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullInterface.lean:51/55/68`；`HaarLogVolume.lean:51-71` 为另一种 log-volume |
| det × log-volume 簿记 | `HullDeterminantLogVolumeReduction.lean:123 HullDeterminantLogVolumeFrozenSpec`、`:173 matrixLogDet`、`:220 packetDiagonalMatrix`、`:249 packetLogVolume_eq_matrixLogDet`、`:302 packetLogVolume_tensorPower` |
| Haar 伸缩 | `CardHullRealHaarDilationDocking.lean`（224 行，green）；`FinitePadicHaarScaling.lean:25/54` |
| 行列式/对偶 | `IntegralTraceDualLattice.lean:75/94/118/270/300` |

## 2. 本任务 Lean 文件（`Mzk1ProductFormulaDegreeActual.lean`，**watchdog DONE EXIT=0，20:33:49Z / 59s**）

```lean
-- 1. product formula（re-export :246/:271）
theorem productFormula_globalScalar (f : Fˣ) :
  (principalDivisorFinite f).sum (fun v n => (n:ℝ) * Real.log (finitePlaceResidueCardinality v))
    + ∑ w : InfinitePlace F, (mult w : ℝ) * archimedeanPlaceValue w f = 0
theorem weightedFiniteSum_eq_archimedeanLogSum_globalScalar (f : Fˣ) : ...

-- 2. 最小 Arakelov degree 接口（定义 + 一致性定理分开）
noncomputable def arakelovDegree (d : SourceModelBackend.ExplicitDivisor F) : ℝ := globalPrimeStripWeight d
noncomputable def arakelovDegreeHom : SourceModelBackend.ExplicitDivisor F →+ ℝ := globalPrimeStripWeightHom
theorem arakelovDegree_eq_hom (d) : arakelovDegree d = arakelovDegreeHom d := rfl
theorem arakelovDegree_add (d e) : arakelovDegree (d+e) = arakelovDegree d + arakelovDegree e
theorem arakelovDegree_zero : arakelovDegree 0 = 0
theorem arakelovDegree_principalUnit (f : Fˣ) : arakelovDegree (principalDivisorExplicit (ofMul f)) = 0

-- 3. degree 差公式
noncomputable def arakelovDegreeDifference (d₁ d₂) : ℝ := arakelovDegree d₁ - arakelovDegree d₂
theorem arakelovDegreeDifference_eq_add (d₁ d₂) : arakelovDegreeDifference d₁ d₂ = arakelovDegree (d₁ - d₂)
theorem arakelovDegreeDifference_principalUnit (d f) :
  arakelovDegreeDifference d (principalDivisorExplicit (ofMul f)) = arakelovDegree d

-- 4. 归一化约定（定义展开）
theorem arakelovDegree_eq_localWeights (d) :
  arakelovDegree d = d.1.sum (fun v n => n * log (#(O_F/v))) + ∑_w [F_w:ℝ] * d.2 w
```

注意：
- `arakelovDegree_eq_localWeights` 是 `rfl` 型（degree 的定义展开），**不是**与 paper 归一化的等式；
- 有限权重用 `log (#(O_F/v))`，arch 权重用 `[F_w:ℝ]`（1 或 2）；paper 的 `1/(2ℓ)` 归一化**未包含**；
- `arakelovDegreeDifference` 的“差公式”目前是**加性/主除子不变性**；paper 的
  `deg(D_Θ) − deg(D_q) = Σ length(C_v) log Nv − Σ_σ n_σ log‖φ‖_σ` 需要 **Θ/q 线丛与 arch 归一化对象**（GAP-DEGREE-BRIDGE + GAP-NORM-ARCH）。

## 3. 与 (C20) / (C17)-(C19) 的接口

| 接口 | 本文件提供 | 仍缺 |
|---|---|---|
| (C17) det=norm | 无（在 `Mzk1NormDeterminantToolsActual`，green） | 无 |
| (C18) 范数函子性 | 无（同上，green 部分） | 项目 relative completion 实例化 |
| (C19) norm-power-log | 无（同上，green） | paper 归一化 |
| **(C20) product formula** | **`productFormula_globalScalar`（re-export 数域乘积公式）** | 独立证明不需要（Mathlib 输入已审计）；但只对全局单位，任意非零元版本未做 |
| **(C20) Arakelov degree** | **最小接口 `arakelovDegree = globalPrimeStripWeight` + 加性/零/主除子不变** | **GAP-DEGREE-BRIDGE**：Example36 显式除子度 ↔ S2717/S2807 theta-hull/q-pilot log-volume 的识别；**GAP-NORM-ARCH**：paper `1/(2ℓ)` 与 arch 归一化 |

## 4. 缺口（精确）

```
GAP-DEGREE-BRIDGE：Example36 的 globalPrimeStripWeight 作用在 ExplicitDivisor F
  （有限位 ℤ-系数 + arch 实数坐标）；我们的 R = S2717ThetaHullLogVolume / A = paperQAbsLog
  是 C3 tensor Haar log-volume / 标量。两者之间的显式桥（区域→除子、log-volume→权重）未构造。
GAP-NORM-ARCH：paper 的 |log q|=(1/(2ℓ))log q 与 arch 归一化（(1/[K:Q]) 等）未进入 degree 接口；
  当前接口是无归一化的 signed place-index 聚合。
GAP-ARB-ELEMENT：product formula 只对 f : Fˣ（全局单位）形式化；任意非零元素版本
  （需要 principal divisor 的有限部分 + 零点/极点）未做。
GAP-DEGREE-DIFF：paper 的 deg(D_Θ) − deg(D_q) 具体差公式需要 Θ/q 线丛的 Hermitian 度量对象，
  本文件只给抽象差公式（加性/主除子不变）。
```

## 5. build 证据

```
dag/watchdog/watchdog.log: L2040xx `2026-11-12T20:33:49.xxxZ DONE EXIT=0 tmp/sheaf/xif/paper/Mzk1ProductFormulaDegreeActual.lean (59s)`
olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1ProductFormulaDegreeActual.olean
```

## 6. 下一步建议

1. 先让 watchdog 编译 `Mzk1ProductFormulaDegreeActual.lean`；FAIL 首错回传；
2. 若通过：把 `arakelovDegree` 与 `HaarLogVolume`/HullDet 簿记的**局部读数**对齐（每个位上的权重 = log-volume 差），
   这是 GAP-DEGREE-BRIDGE 的第一步；
3. (C20) 的 paper 归一化（GAP-NORM-ARCH）可复用 `Mzk1NormDeterminantToolsActual.norm_pow_log_relation` 的 log 线性化；
4. 任意非零元 product formula：在 `principalDivisorExplicit` 的零点/极点分解上扩展（需新的除子结构，暂不做）。
---

## 7. task-97：GAP-DEGREE-BRIDGE q 侧桥（更新）

| field | value |
|---|---|
| Lean | `tmp/sheaf/xif/paper/Mzk1DegreeBridgeActual.lean`：**watchdog DONE EXIT=0**（`watchdog.log` L204190，`2026-11-12T20:39:22.606Z`，37s；olean 存在） |
| 已证（q 侧，全部 green） | 1) `paperQPilotLogVolume_multi_eq_sourceSigned`（re-export `S2708:153`）；2) `paperQPilotLogVolume_multi_eq_neg_badQ`（`:161`）；3) `stageAQParameterSigned_multi_eq_volume`（`S2717StageAMultiQActual:212`）；4) `qProduct_log_eq_sum`（`:169`）；5) `paperQPilotLogVolume_multi_eq_neg_abs_qProduct_log`（`:190`）；6) 条件桥 `paperQPilotLogVolume_multi_eq_neg_degree`、`sourceQPilotSignedLog_eq_neg_degree`；7) product-formula 一致性 `sourceBadQAbsLog_eq_zero_of_principal` |
| 桥的精确形式 | `QPilotDegreeBridge (d) : globalPrimeStripWeight d = sourceBadQAbsLog I.initial`；在此假设下 `paperQPilotLogVolume_multi D = -globalPrimeStripWeight d`（真证） |
| GAP-DEGREE-BRIDGE-Q | 未构造 `badPlaces → HeightOneSpectrum (𝓞 F)` 的 place map 与 `|log q_b| = ν_v log #(O_F/v)` 的逐位等式；`QPilotDegreeBridge` 是该识别的显式接口 |
| GAP-S2717-BRIDGE | `S2717QPilotLogVolume` 经 `S2711I` 的 initial 定义；与通用 `I` 的 initial 识别未构造 |
| GAP-THETA-DEGREE | theta 侧 `S2717ThetaHullLogVolume`/`S2807` 与 Example36 degree 的桥未做（q 侧已给形式，theta 侧需 Haar/C3 区域读数） |
---

## 8. task-99：GAP-DEGREE-BRIDGE-Q 的 place map 与逐位 valuation（**task-99 completed / green**）

| field | value |
|---|---|
| Lean | `tmp/sheaf/xif/paper/Mzk1QPilotPlaceDegreeActual.lean`：**watchdog DONE EXIT=0**（`watchdog.log` 20:48:23Z，58s；olean 存在） |
| 实际 place map | **`nativeBadToFinitePlace := qVFamTensorPlace T`**，其定义 `qVFamTensorPlace T b := (nativeBadLift T).lift b`（`QVFamTensorCoefficientActual.lean:47`）——badPlaces → `NumberField.FinitePlace T.arithmetic.F` 的**实际映射**（非 Prop） |
| 逐位等式 | **`nativeBadPlace_abs_log_eq`**：`|log (qVFamDefaultNorm T b)| = qVFamTensorCoefficient T b * log (residueNormBase (qVFamTensorPlace T b))`（真证；复用 `localLogMagnitude_eq_order_mul_log` + `localLogMagnitude_qVFamily_eq` + `localLogMagnitude_pos`） |
| 有理素数形式 | `nativeBadPlace_abs_log_eq_logP`（需显式 `hres : residueNormBase place = qVFamTensorP`） |
| sum 形式 | `nativeBadQAbsLogSum_eq_valuationSum`（真证）；`nativeBadQAbsLogSum_eq_valuationSum_logP`（`hres` 逐位） |
| source-q 接口 | `sourceBadQAbsLogFamily_eq_valuationSum`：若契约 q-参数族与 native qVFamily 范数逐位 `|log|` 相等（显式 `hf`），则 source bad-q abs log = native valuation sum（真证，条件式） |
| GAP-SOURCE-NATIVE-Q | 契约 `I.initial.reduction.qParameter`（抽象 Real 族、badPlaces 抽象 Type）与 native `qVFamDefaultNorm`（实际 qVFamily）的 index+values 识别未构造；`hf` 是精确接口 |
| GAP-DEGREE-EXPLICIT | 尚未构造 `SourceModelBackend.ExplicitDivisor F`（badPlaces → HeightOneSpectrum 的 Finsupp、arch 零）并证明 `globalPrimeStripWeight d = nativeBadValuationSum`；这是接 Example36 degree 的下一步 |
| GAP-DEGREE-RES | `residueNormBase place = qVFamTensorP`（degree one/obstruction 条件）需单独证明（`BadPlaceNormalizedSourceHypothesisActual:85 logResidueNormBase_eq_logP_of_obstruction_degree_one` 提供 log 形式，可转不等式/相等） |
---

## 9. task-101：GAP-DEGREE-EXPLICIT（单 place 构造）（**task-101 completed / green**）

| field | value |
|---|---|
| Lean | `tmp/sheaf/xif/paper/Mzk1DegreeExplicitActual.lean`：**watchdog DONE EXIT=0**（`watchdog.log` 20:53:38Z，55s；olean 存在） |
| 构造 | **`nativeBadExplicitDivisor T b`**：`ExplicitDivisor F = (Finsupp.single (nativeBadHeightOne T b) (nativeBadIntCoeff T b), fun _ => 0)`；`nativeBadHeightOne := NumberField.FinitePlace.equivHeightOneSpectrum (qVFamTensorPlace T b)`；`nativeBadIntCoeff := ((qVFamily T b).order : ℤ)`。**真实数据，非 Prop 占位**。 |
| 已证 | `nativeBadIntCoeff_cast`（ℤ 系数 cast 到 ℝ = qVFamTensorCoefficient）；`globalPrimeStripWeight_nativeBadExplicitDivisor`（在 `hcard` 下 weight = order_b·log(residueNormBase place_b)）；`..._eq_abs_log`（在 hcard 下 weight = `|log(qVFamDefaultNorm b)|`，用 Mzk1QPilotPlaceDegreeActual 的逐位等式）。 |
| GAP-DEGREE-CARD | `finitePlaceResidueCardinality (nativeBadHeightOne b) = residueNormBase (qVFamTensorPlace b)`（HeightOneSpectrum 与 FinitePlace 的剩余基数桥）未证；作为显式 `hcard` 假设。 |
| GAP-DEGREE-SUM | **全 bad 索引的和**（`∑_b order_b log residueNormBase` = `nativeBadValuationSum`）需要 `Finsupp.single` 之和的 sum-additivity 构造（`Finsupp.sum_finset_sum` 型引理），当前只做了单 place 块。 |
| 与 task-99/97 的关系 | 单 place：weight = `|log q_b|` = task-99 逐位等式；全和后可得 `globalPrimeStripWeight d_bad = nativeBadValuationSum`，再接 task-97 的 `paperQPilotLogVolume_multi = −globalPrimeStripWeight`。 |
---

## 10. task-105：GAP-DEGREE-SUM + GAP-DEGREE-CARD（**task-105 completed / green**）

| field | value |
|---|---|
| Lean | `tmp/sheaf/xif/paper/Mzk1DegreeSumActual.lean`：**watchdog DONE EXIT=0**（`watchdog.log` 21:04:51Z，56s；olean 存在） |
| GAP-DEGREE-CARD | **已闭（attempt）**：`finitePlaceResidueCardinality_nativeBadHeightOne : (finitePlaceResidueCardinality (nativeBadHeightOne T b) : ℝ) = residueNormBase (qVFamTensorPlace T b)`；证明用 `NumberField.FinitePlace.equivHeightOneSpectrum_apply`（Mathlib `NumberField/Completion/FinitePlace.lean:400-407`）+ `Ideal.absNorm_apply` + `Submodule.cardQuot_apply`。 |
| 全求和构造 | `nativeBadFiniteDivisor := ∑_b Finsupp.single (nativeBadHeightOne T b) (nativeBadIntCoeff T b)`（`HeightOneSpectrum →₀ ℤ`）；`nativeBadExplicitDivisorSum := (nativeBadFiniteDivisor, fun _ => 0)`。真实数据。 |
| 已证（attempt） | `nativeBadFiniteDivisor_sum_weight`（Finset.sum of singles 的 `.sum` 展开，用 `Finsupp.sum_add_index'` + `Finsupp.sum_single_index` + 归纳）；`globalPrimeStripWeight_nativeBadExplicitDivisorSum : weight = nativeBadValuationSum`；`..._eq_absLogSum : weight = nativeBadQAbsLogSum`（用 task-99 的 `nativeBadQAbsLogSum_eq_valuationSum`）。 |
| 剩余 GAP | GAP-SOURCE-NATIVE-Q（task-99 §4）：native `qVFamDefaultNorm` 族 vs 契约 `qParameter` 族的 index+values 识别；接上后 `paperQPilotLogVolume_multi = -weight` 可无条件化（native 数据侧）。 |
---

## 11. task-114：GAP-SOURCE-NATIVE-Q（S1487 canonical 情形）（**task-114 completed / green（条件式）**）

| field | value |
|---|---|
| Lean | `tmp/sheaf/xif/paper/Mzk1SourceNativeQActual.lean`：**watchdog DONE EXIT=0**（`watchdog.log` 21:36:45Z，61s；olean 87544 B）；本版为条件式（`hsrc` 显式）——单 index、`hsrc : OrigXiFPaperBadQAbsLog S1487FaithfulSourceData = |log qVFamDefaultNorm default|` ⇒ `= nativeBadQAbsLogSum`。 |
| S1487 契约值 | `S1487_qParameter_eq_norm : (S1487FaithfulSourceData).reduction.qParameter b = ‖S1487Cand.q‖`（rfl；`S1487OQPilotScalarEqualityActual:520`，badPlaces=PUnit, qParameter=fun _ => ‖S1487Cand.q‖）；`S1487_badQAbsLog_eq_abs_log_norm`。 |
| 桥接口 | `S1487NativeQIdentification T b : |log (S1487 qParameter)| = |log (qVFamDefaultNorm T b)|`（显式条件）；`S1487_abs_log_eq_qVFamDefaultNorm_abs_log`（展开）。 |
| 单 index 求和桥 | `S1487_sourceBadQAbsLog_eq_nativeBadQAbsLogSum`：`[Unique (Bad (nativePlaceSelection T))]` + 逐位识别 ⇒ `OrigXiFPaperBadQAbsLog S1487FaithfulSourceData = nativeBadQAbsLogSum T`（真证条件式，接 task-99/105 degree sum 输入）。 |
| 剩余 GAP-SOURCE-NATIVE-Q（general） | 一般 badPlaces ↔ Bad (nativePlaceSelection T) 的 index map，以及逐位 `qParameter b = ‖qVFamily b .q‖` 的几何构造未做；S1487 canonical 只给值 + 条件桥，索引/放置识别仍需 native place map 与 clause-B q 的选择对齐。 |
---

## 12. task-119：P6-A (C17) WeightedDeterminantPacket 实例化（新增，待 watchdog）

| field | value |
|---|---|
| Lean | `tmp/sheaf/xif/paper/Mzk1WeightedDetPacketActual.lean`（新文件；已加入 watchdog 名单；**DONE EXIT=0 21:23:33Z**） |
| 已证的 packet 接口 | `commonTensorDegree_eq_of_denominator_eq`；`weightedLogVolume_sub_eq_commonTensorDegree_mul_normalized_sub : P.weighted − Q.weighted = N·(P.normalized − Q.normalized)`（P/Q 同一 denominator family）；`c17_profileArithmeticDegree_adjustedDetTensorPower`（re-export `HullDeterminantLogVolumeReduction.profileArithmeticDegree_adjustedDetTensorPower`） |
| 条件 (C17) | `weightedLogVolume_sub_eq_commonTensorDegree_mul_M`：若 `GAP_P6_C17_DICT` 成立且 `thetaActual − qActual = M`，则 `Q.weighted − P.weighted = N·M`；GAP 是显式定理假设，不是 structure 字段 |
| 命名缺口 | `GAP-P6-C17-DICT`：`P.normalizedLogVolume = qActual ∧ Q.normalizedLogVolume = thetaActual`，其中 qActual/thetaActual 是实际 q/Θ normalized readings；**本包未构造这条实际识别**，因为不能把任意 packet 字段冒充 paper 读数。 |
| 实际 q 侧已有输入 | `QVFamTensorCoefficientActual:76 qVFamTensorCoefficient = order(qVFamily)`；`QVFamRootFactorCorrectionActual:56 qVFamPaperRootCoefficient = order/(2l)`；`Mzk1DegreeBridgeActual` 的 q 侧 degree 桥、`Mzk1DegreeSumActual` 的 `globalPrimeStripWeight_nativeBadExplicitDivisorSum` 可作为 qActual 的候选读数，但尚需把它们显式接到 packet.normalizedLogVolume。 |
| 实际 Θ 侧已有输入 | `BadPlacePaperRootThetaHullActual:45 paperRootThetaHullLog`/`:51 paperRootThetaFormulaLog`（带 `PaperRootHullFormulaGap`）；`qVFamPaperThetaTensorCoefficient`（RootFactorCorrection:61）。这些是实际 Θ 侧候选，但与 packet.normalizedLogVolume 的等式正是 GAP-P6-C17-DICT。 |
| 诚实边界 | 没有把 `weightedDeterminantNormalization` Obligation 当证明；没有实际 q/Θ packet 冒充；没有新增结构字段/目标假设。 |
| 验收 | **watchdog DONE EXIT=0 21:23:33Z（35s）**，olean 存在；源码 grep 无 sorry/admit/axiom。`#print axioms` 未运行（统一交给后续 gate 验收）。 |

下一步：若 watchdog 首错在 import/API，按 log 修；若通过，再把 qActual 接到 `Mzk1DegreeBridgeActual`/`Mzk1DegreeSumActual` 的已有桥、thetaActual 接到 `paperRootThetaHullLog` 的 `PaperRootHullFormulaGap`，优先把 GAP-P6-C17-DICT 拆成两条更小的 named input。

---

## 12. GAP-NORM-ARCH 关联：arch-normalized degree（green）

`tmp/sheaf/xif/paper/Mzk1NormArchDegreeActual.lean` **watchdog DONE EXIT=0**（21:48:57Z，59s；`Mzk1NormArchDegreeActual.olean`）。
定义 `archNormalizedDegree c d`（Example36 显式除子度的 arch 部乘 c），证明：c=1 回到 `globalPrimeStripWeight`；零度（product formula/主除子）⇒ `(c-1)·arch 和`；principal-unit 特化。剩余：paper `1/[K:Q]`/`1/(2ℓ)` 与 c 的识别，arch 和 ↔ S2717/S2807 读数桥。

---

## 13. task-119 P6-B1：具体 WeightedDeterminantPacket 实例（新增 green）

| field | value |
|---|---|
| Lean | `tmp/sheaf/xif/paper/Mzk1WeightedDetPacketInstanceActual.lean`：**watchdog DONE EXIT=0 21:50:23Z（62s）**；olean 163,376 B；源码 grep 无 sorry/admit/axiom |
| q packet | `qPacket`，label = `Bad (nativePlaceSelection T)`；`hullLogDegree b = -baseQLogMagnitude T b`（`BaseQLogVolumeActual:49` 实际 signed q log）；`structureSheafLogDegree = 0`；`denominator = 2*l`（`paperRootDenominator`） |
| Θ packet | `thetaPacket`，同 label；`hullLogDegree b = -∑_j qVFamThetaTensorCoefficient T b j () * log(qVFamTensorP T b)`（`QVFamTensorCoefficientActual:76/89` 实际 classical Θ 系数和）；同 denominator `2*l` |
| 清分母常数 | `qPacket_commonTensorDegree` / `thetaPacket_commonTensorDegree`：二者 commonTensorDegree = `(2*l)^Fintype.card (Bad ...)`；与 paper root denominator `2*l` 一致 |
| normalized q | `qPacket_normalizedLogVolume : qPacket.normalized = -(∑_b baseQLogMagnitude T b)/(2*l)` |
| normalized Θ | `thetaPacket_normalizedLogVolume : thetaPacket.normalized = (∑_b thetaHullLogDegree T b)/(2*l)` |
| DegreeBridge/DegreeSum 对齐候选 | `qActualNormalized := -nativeBadQAbsLogSum T/(2*l)`（`Mzk1QPilotPlaceDegreeActual:100` + `Mzk1DegreeSumActual:102` 的实际 degree weight）；`thetaActualNormalized := (∑ thetaHullLogDegree)/(2*l)`（实际 classical Θ 候选） |
| 命名缺口 | **`GAP_P6_C17_DICT_INST`**：`qPacket.normalized = qActualNormalized ∧ thetaPacket.normalized = thetaActualNormalized`。这是 `Prop` 定理假设，不是 structure 字段；本包未冒充 paper Θ 读数 |
| 条件 (C17) | `c17_instance_weightedDiff_eq_mul_M`：在 `GAP_P6_C17_DICT_INST` 与 `thetaActual−qActual=M` 下，`thetaPacket.weighted − qPacket.weighted = (2l)^#Bad * M`；N 为实际清分母常数 |
| 与 P6-A 的关系 | P6-A 给通用 packet 接口恒等式；本节给具体 q/Θ 两个 packet 实例和实际清分母常数；实际读数识别仍由 GAP-P6-C17-DICT-INST 命名 |
| 诚实边界 | 没有新增 structure 字段；没有把 `weightedDeterminantNormalization` Obligation 当证明；没有新增假设换 green |

下一步：优先把 `GAP_P6_C17_DICT_INST` 拆成 (a) qPacket.normalized ↔ `nativeBadQAbsLogSum/(2l)`（DegreeSum 实际权重）与 (b) thetaPacket.normalized ↔ `paperRootThetaHullLog`/`paperRootThetaFormulaLog` 的 `PaperRootHullFormulaGap` 两条更小 named input；不要直接用 V4 candidate 或 P7 结论。

### 13.1 q 侧 DICT-INST 检查（2026-11-13）

- **不能直接 rfl**：`baseQ := nativeBaseQFamily`（`BaseQFamilyActual:59`）是 V_bad 的 section lift 上的独立 q candidate；该文件 :20-22 明确 `No equality to qVFamily is asserted`。
- `nativeBadQAbsLogSum` 使用 `qVFamDefaultNorm = ‖(qVFamily T b).q‖`（`QVFamNormalizedCoefficientBridgeActual:59`）；`baseQLogMagnitude` 使用 `localLogMagnitude (baseQ T b)`（`BaseQLogVolumeActual:49`）。两者不是同一对象。
- 已在 `Mzk1WeightedDetPacketInstanceActual` 新增：
  - `qActualBaseNormalized := -baseQTotalLogMagnitude/(2l)`；
  - `qPacket_normalized_eq_qActualBase : qPacket.normalized = qActualBaseNormalized`（PROVED，纯 base-q 侧）；
  - **`GAP_P6_C17_QHALF : baseQTotalLogMagnitude = nativeBadQAbsLogSum`**（精确 q 侧命名缺口，不是 structure 字段）；
  - `qPacket_normalized_eq_qActualNormalized_of_qhalf`：在 QHALF 下 qPacket.normalized = qActualNormalized（即 q 半不再直接假设，而是归约为 QBase↔qVFamily 的实际对象识别）。
- 结论：**q 半不能无条件证明**，但已精确拆成 `GAP-P6-C17-QHALF`；Θ 半仍是 `GAP_P6_C17_DICT_INST` 的另一半（paperRootThetaHullLog/FormulaLog 的识别）。
- **build 证据**：加 q-half 后 watchdog **DONE EXIT=0 21:58:38Z（59s）**，olean 存在；源码无 sorry/admit/axiom。

### 13.2 Θ 侧候选读数 vs `paperRootThetaHullLog`（识别分析）

- θPacket 的 normalized 读数（本文件已证）：
  `thetaPacket.normalized = (∑_b thetaHullLogDegree T b)/(2l)`，
  其中 `thetaHullLogDegree T b = -∑_j qVFamThetaTensorCoefficient T b j () * log(qVFamTensorP T b)`。
- 因 `qVFamThetaTensorCoefficient T b j () = j²·order_b`（`QVFamTensorCoefficientActual:89`），故
  `thetaPacket.normalized = -∑_b ∑_j j²·order_b·log(qVFamTensorP T b)/(2l)`
  = `-∑_b ∑_j qVFamPaperThetaTensorCoefficient T b j · log(qVFamTensorP T b)`（在 `qVFamPaperThetaTensorCoefficient = j²·order/(2l)`，`QVFamRootFactorCorrectionActual:61` 的意义下）。
- 实际 Θ 侧 `paperRootThetaHullLog T b mu`（`BadPlacePaperRootThetaHullActual:45`）是 `rootThetaHullLog`，其公式版
  `paperRootThetaFormulaLog T b = -((∑_j qVFamPaperRootCoefficient T b) · log(qVFamTensorP T b))`（同文件 :51-54），
  其中 `paperRootCoefficientFamily T b` 对 `qVFamTensorV=Unit` 只放一个 root coefficient，**不带 j² 求和**。
- 因此两个候选差两层，不能当同一个读数：
  1. **系数层**：θPacket 用 `∑_j j²·rootCoeff`；paperRootThetaFormulaLog 用 `card · rootCoeff`（或单个 root）；差 `(∑_j j² - card)·rootCoeff·log p`，一般非零。
  2. **hull 层**：`paperRootThetaHullLog` 还要 `PaperRootHullFormulaGap`（`ArithmeticTuplePureFractionalScalingData` + `hull_eq`），`paperRootThetaFormulaLog` 只是该 gap 下的公式，不是 hull 体积本身。
- 精确缺口命名：**`GAP_P6_C17_THETA`** = `(thetaPacket.normalized = thetaActualNormalized) ∧ (thetaActualNormalized 与 paperRootThetaHullLog/FormulaLog 的系数层+hull层识别)`；在 `Mzk1WeightedDetPacketInstanceActual` 中仍由 `GAP_P6_C17_DICT_INST` 的 Θ 半承担，没有冒充 paper 读数。
- 下一步可写：把 `thetaActualNormalized` 用 `qVFamPaperThetaTensorCoefficient` 重写（定义性），再把 `paperRootThetaFormulaLog` 的 `j²`/`rootCoeff` 差异作为命名引理；若需要 hull 体积还需引入 `PaperRootHullFormulaGap`，不能直接当定理输入。

### 13.3 Θ 侧 canonical 参照：S3137 raw vs packet 读数（新口径 2026-11-13 06:0x）

按 Lead 口径，θ 侧不再用旧 S800 `paperHullLog` 作参照；canonical 是：
- `S3137QThetaPilotLogVolumeReadingsActual:128`：
  `thetaPilotHullLogVolumeReal C3 = Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal`；
- `S3137ThetaHullVolumeScalingActual:70`：
  `thetaPilotHullLogVolumeReal C3 = Real.log ((actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3)).toReal`（因 `thetaPilotHull_eq_region`）；
- `Mzk1HolomorphicHullLogVolumeReconciliationActual:37-44` 的 7 missing 清单，其中第 5 项正是：
  **`theta raw Haar vs paper normalized V (factor [C3 block : Q_p] and C3-vs-D dictionary)`**。

本 packet 的 θ 候选读数是：
  `thetaActualNormalized T = (∑_b thetaHullLogDegree T b)/(2l)`，
  `thetaHullLogDegree T b = -∑_j qVFamThetaTensorCoefficient T b j () * log(qVFamTensorP T b)`，
即**按 qVFamily order/坏位/标签的系数-对数 p 和**，不是 Haar 体积。

与 S3137 raw 的差异分层（精确缺口 **`GAP-P6-C17-THETA-S3137`**）：

1. **符号/归一化约定**：S3137 `thetaPilotHullLogVolumeReal` 是 `log Haar(region)`（raw 无符号）；packet 候选是 `-∑ ...` signed 形式；paper 的 `-|log Θ|` 需要先证明 `-thetaPilotHullLogVolumeReal`（或 raw 的符号/绝对值）与 packet signed 读数一致。
2. **Haar 体积 vs 系数和**：S3137 是 actual `actualC3LogShellTensorHaar` 对 `actualC3LogShellTensorRegion` 的 Haar log；packet 是 `qVFamThetaTensorCoefficient` 乘 `log p` 的和；缺 `actual region Haar log = -∑_b∑_j coeff·log p` 的实际 region/hull 归一化恒等式（`paperRootThetaHullLog` 仅给 `PaperRootHullFormulaGap` 下的公式，不是 S3137 raw）。
3. **block/arch 因子**：S3137 p-scaling 给 `-[c3TensorBlockDimension C3 : ℝ] * log p`（`S3137ThetaHullVolumeScalingActual:59-64`）；packet 用 `2l` denominator 与 `qVFamTensorP`，缺 `[C3 block : Q_p]`/block dimension 的归一化因子。
4. **C3 ↔ D/native 字典**：S3137 的 `C3 : SourcePilotRegionData` 是抽象 C3 输入；packet 用 native bad index/qVFamTensorPlaces；缺 C3-vs-D 与 native place/block 的识别（reconciliation missing #5 的后半）。
5. **hull/carrier**：S3137 hull = actual C3 region（`thetaPilotHull_eq_region`）；packet 无 region/measure，paperRootThetaHullLog 还额外需要 `PaperRootHullFormulaGap` 的 Data/hull_eq；不能把 FormulaLog 当 S3137 raw。

结论：**`thetaActualNormalized` 与 S3137 raw 不是同一个读数**；不能把 `paperRootThetaFormulaLog`/旧 S800 作为中间桥。精确命名缺口 `GAP-P6-C17-THETA-S3137` 由上述 1–4 层组成；当前 packet 文件保持 CONDITIONAL，q 侧另有 `GAP-P6-C17-QHALF`。

#### 13.1a QHALF 精确拆分（在 import 现有 K-side 缺口对象后）

- `baseQ` 的 underlying place 是 `nativeBaseSectionPlace T b = sectionFiniteLift (nativePlaceSelection T) b.1`（`BaseQFamilyActual:52-55`）；
- `qVFamily` 的 underlying place 是 `(nativeBadLift T).lift b`（`QPilotZeroLocusDivisorActual:55-57`，由 `clauseB.q_comparison` Classical.choice）；
- 现有 `S605KSideQVActual:6-9` 明确：`qVFamilyKLift`（Classical.choose of comap surjectivity）与 paper spec 的 `sectionFiniteLift` **placement equality 未证**；`S618KSideQVPlaceActual:31-47` 把 place/shadow 识别记成 `KSideQVPlaceGap`/`KSideQVComparisonData`；
- 更关键：即便 place 相同，`badPlaceQCandidate`（baseQ）与 `clauseB.q_comparison.parameter`（qVFamily）仍是**不同构造的 FinitePlaceQCandidate**；`BaseQFamilyActual:20-22` 明确 no equality，`S605` 的 `qSection_eq/order_eq` 也需要显式数据。

因此 `GAP_P6_C17_QHALF` 至少拆成两个独立缺口：
1. **`GAP-P6-C17-QPLACE`**：`sectionFiniteLift (nativePlaceSelection T) b.1 = (nativeBadLift T).lift b`（place/shadow equality；`S618` 的 `place_eq_imp_shadow_eq` 给条件方向，未给无条件）；
2. **`GAP-P6-C17-QCAND`**：`badPlaceQCandidate (nativePlaceSelection T) b` 与 `qVFamily T b` 的 order/norm/log 候选相等（`FinitePlaceQCandidate` 层；`BaseQFamilyActual` 明确 independent；`S605` 的 qSection/order 数据也未证）。

结论：QHALF 不能由现有 green 定理直接推出；不再尝试用 unfold/simp 伪造。当前 `GAP_P6_C17_QHALF` 保留为总缺口，以上两子缺口为精确 audit 记录。

#### 13.1b QPLACE comap 形式（PROVED）与 place equality 的剩余缺口

- 已加入 `Mzk1WeightedDetPacketInstanceActual.lean`：
  `qplace_comap_eq : NumberFieldFinitePlace.comap (sectionFiniteLift (nativePlaceSelection T) b.1) = NumberFieldFinitePlace.comap ((nativeBadLift T).lift b)`，
  证明只用 `sectionFiniteLift_comap` 与 `(nativeBadLift T).lift_comap`；watchdog **DONE EXIT=0 22:12:50Z（65s）**，olean 202,056 B。
- **place equality 本身仍不能证**：`sectionFiniteLift` 是 `V_section.lift` 上的 `Classical.choose`（`SourcePlacePartitionReduction:322`），`nativeBadLift.lift` 是 `comap_surjective` 的 `Classical.choose`（`NativeBadLiftActual:22`）；两者只有 comap 相同，place 是不同 choice。`S605KSideQVActual:6-9` 已记录同一类 place-choice gap。
- 因此 **QPLACE 未关闭**：comap 形式已证；剩余精确缺口是 `sectionFiniteLift ... = (nativeBadLift T).lift b`（需 lift/choice agreement 或唯一 lift 条件），以及其后的 `GAP-P6-C17-QCAND`（candidate order/norm 相等）。QHALF 继续保留。

#### 13.1c QPLACE/QCAND 显式化（最终版本，2026-11-13 06:22）

重要更正：`sectionFiniteLift` 返回 `FinitePlace A.K`，`nativeBadLift.lift` 返回 `FinitePlace A.F`，**字面量类型不同**，不能直接相等。QPLACE 的正确同载体形式是 `fkDescentShadow`（F-shadow of section K-place）与 `nativeFPlace` 的 F-place equality：

- `def GAP_P6_C17_QPLACE (b) : Prop := fkDescentShadow (nativePlaceSelection T) b.1 = (nativeBadLift T).lift b`（`Mzk1WeightedDetPacketInstanceActual:70`）；
- `qplace_comap_eq`（PROVED，:59）：`comap (sectionFiniteLift ...) = comap ((nativeBadLift T).lift b)`；它是 **comap 形式**，不是 place equality；
- `def GAP_P6_C17_QCAND : Prop := ∀ b, baseQLogMagnitude T b = |Real.log (qVFamDefaultNorm T b)|`（:76）；
- `def GAP_P6_C17_QHALF : Prop := baseQTotalLogMagnitude T = nativeBadQAbsLogSum T`（:85）；
- **`QHALF_of_QPLACE_QCAND`（PROVED，:90）**：QPLACE（∀b）+ QCAND ⇒ QHALF；
- **`qPacket_normalized_eq_qActualNormalized_of_qplace_qcand`（PROVED conditional，:215）**：q-half 现在以 QPLACE + QCAND 为两个显式输入，不再只用一个 QHALF 假设。

build 证据：watchdog **DONE EXIT=0 22:22:09Z（60s）**；olean 239,232 B；源码无 sorry/admit/axiom。

QPLACE 不可证的 exact 理由：`sectionFiniteLift` 是 `V_section.lift` 的 `Classical.choose`（SourcePlacePartitionReduction:322），`nativeBadLift.lift` 是 `comap_surjective` 的 `Classical.choose`（NativeBadLiftActual:22）；二者只共享 comap；`S1413SourceKPlaceQComparisonActual:59-63` 也将 `fkDescentShadow = nativeBadLift.lift` 记为未证且未假设的 `S1413ShadowEqualsNative`。

#### 13.1d QCAND 可证化尝试：不能直接证，已精确拆成 ORDER + RESNORM

- `qcand_iff_order_residue`（PROVED）：
  `baseQLogMagnitude T b = |log(qVFamDefaultNorm T b)|`
  ↔ `(baseQ T b).order * log(residueNormBase (nativeBaseSectionPlace T b))`
    `= qVFamTensorCoefficient T b * log(residueNormBase (qVFamTensorPlace T b))`；
  证明直接用 `BaseQLogVolumeActual:74 baseQLogMagnitude_eq_order_mul_log` 与 `Mzk1QPilotPlaceDegreeActual:64 nativeBadPlace_abs_log_eq`。
- 因此 QCAND 精确拆成：
  1. **`GAP_P6_C17_QCAND_ORDER`**：`(baseQ T b).order = (qVFamily T b).order`；
  2. **`GAP_P6_C17_QCAND_RESNORM`**：`residueNormBase (nativeBaseSectionPlace T b) = residueNormBase (qVFamTensorPlace T b)`；
- `QCAND_of_order_resnorm`（PROVED）：ORDER + RESNORM ⇒ QCAND。
- 为什么不能直接 unfold：`baseQ` 与 `qVFamily` 是不同 `FinitePlaceQCandidate` 构造（section K-place vs clauseB F-place）；两者 q 元素/place 不同，只有 log 量的乘积可能相等；ORDER/RESNORM 均无现成定理。
- 因此 QCAND **未关闭**，但已化为两个可寻址的实际数论缺口；QPLACE 仍是 place/choice 缺口。

#### 13.1e 批量小文件编译结果（2026-11-13 06:46）

- `Mzk1C17QCANDOrderResidueActual`：**DONE EXIT=0 22:44:05Z（100s）**，ole 72,872 B；`qcandAt_iff_order_residue`（PROVED），ORDER/RESNORM 两个命名缺口，`qcand_of_order_resnorm`（PROVED）。
- `Mzk1C17QCANDAssemblyActual`：**DONE EXIT=0 22:46:21Z（77s）**，ole 存在；`qcand_assembly`（ORDER+RESNORM ⇒ QCAND）。
- `Mzk1S3137ThetaRawEqActual`：**DONE EXIT=0 22:44:07Z（102s）**，ole 79,424 B；`thetaRaw_eq_log_actualRegion`（S3137 raw canonical）+ `thetaBlockLogFactor` + `thetaRaw_smul_p_eq_factor_add`（p-scaling 条件 green）。
- `Mzk1S3137ThetaPacketRawGapActual`：**DONE EXIT=0 22:38:36Z（28s）**，ole 71,032 B；`GapThetaPacketRaw packetTheta rawHaarLog := packetTheta = -rawHaarLog` 命名 GAP + defect-zero iff。
- `Mzk1C17QPLACEChoiceGapActual`：**DONE EXIT=0 22:39:46Z（98s）**，ole 50,560 B；`QPlaceChoiceGap`（fkDescentShadow = nativeBadLift.lift）+ `qplace_comap_eq`（PROVED）+ QPLACE⇒comap。
- `Mzk1WeightedDetPacketInstanceActual`：**DONE EXIT=0 22:44:52Z（92s）**，ole 284,592 B；QPLACE/QCAND/QHALF 分解与 q-half 双输入定理全部保留。

#### 13.1f 下一批小文件编译结果（2026-11-13 07:03）

- `Mzk1C17QCANDOrderCoeffActual`：DONE 23:02:52Z（84s），ole 32,592B；ORDER gap 写成 coefficient 等式（`orderGap_imp_coefficient_eq`）。
- `Mzk1C17QCANDResNormLogActual`：DONE 23:02:52Z（84s），ole 29,592B；RESNORM gap 写成 log residue 等式。
- `Mzk1S3137ThetaDefectNormActual`：DONE 22:57:49Z（52s），ole 78,968B；`thetaDefect=packet+raw`，absolute defect=0 ↔ GapThetaPacketRaw。
- `Mzk1C17QPLACELiftUniqueActual`：DONE 23:02:51Z（82s），ole 38,256B；`PlaceLiftUnique ⇒ QPLACE`（k=1/唯一 lift 条件分析，未证明唯一性）。
- `Mzk1P6C17GapLedgerActual`：DONE 22:53:27Z（24s），ole 42,840B；QPLACE/QCAND ORDER/RESNORM/QHALF/THETA-S3137 的 named-gap ledger。

结论：QPLACE/QCAND 仍未被无条件证明；当前状态是 **QPLACE = place-choice gap**，**QCAND = ORDER + RESNORM**，QHALF = QPLACE+QCAND（分解已证），Θ 侧 = S3137 raw 四层差异。
#### 13.1g 下一批 5 份编译结果（2026-11-13 07:21）

- `Mzk1C17QCANDOrderDefsActual` DONE 23:20:34Z：baseQOrder/qVFamOrder 定义对照；
- `Mzk1C17QCANDOrderDefEqActual` DONE 23:20:34Z：ORDER gap ↔ coefficient 等式；
- `Mzk1C17QCANDResNormComapActual` DONE 23:20:34Z：log residue = f * log(lower residue)；`ResNormDegreeGap`（f_K=f_F）命名 GAP；
- `Mzk1S3137ThetaDefectFactorActual` DONE 23:19:41Z：packetFactor/rawFactor 的 defect 因子分解；
- `Mzk1S3137ThetaBlockFactorNonposActual` DONE 23:20:35Z：block log-p factor ≤ 0。

外部搜索记录：Mathlib 只有 `FinitePlace.comap_surjective`，未找到唯一 lift 定理；外部 flt/TauCeti 也未找到可移植的 unique-lift 结果。QPLACE 的充分条件 `PlaceLiftUnique ⇒ QPLACE` 已自写（`Mzk1C17QPLACELiftUniqueActual`）；QPLACE 本身仍未证。QQCAND ORDER/RESNORM 仍为两个 named gap。

#### 13.1h k=1 条件 ORDER/RESNORM 编译结果（2026-11-13 07:48）

- `Mzk1C17QCANDOrderK1Actual` DONE 23:44:03Z（75s），ole 存在：用 S1413 `sectionQ_order`/`shadowQ_order_eq_of_shadow_eq`；在 QPLACE + `eSource=1` + `badPlaceQCandidate.order=sectionQ.order` 下证 `baseQ.order=qVFamily.order`，并给全局 `QCANDOrderGap`。
- `Mzk1C17QCANDResNormDegreeOneActual` DONE 23:48:00Z（75s），ole 存在：用 `residueNormBase_eq_lower_pow` + `nativeBaseSectionPlace_comap` + `nativeBadLift.lift_comap`；两边 `localResidueDegree=1` ⇒ `residueNormBase` 相等，进而 `QCANDResNormGap`。
- 两者均无 sorry/axiom；仍未证明 `eSource=1`/`localResidueDegree=1` 本身。FLT 仓库内 `DedekindDomain/Completion/BaseChange.lean:718/751` 有 `inertiaDeg_eq_inertiaDeg`/`ramificationIdx_mul_inertiaDeg_eq_finrank`，但该 port 当前 watchdog 失败，不能作为现成 olean 输入。

#### 13.1i eSource=1 / localResidueDegree=1 的定性（2026-11-13 07:50）

- `eSource=1` 与 `localResidueDegree=1` 是 **irreducible arithmetic input**（算术非平凡性输入），不能从 Mathlib/FLT 现有定理推出：它们等价于“所选 bad place 的 ramification index / residue degree = 1”。
- FLT 只提供 `inertiaDeg_eq_inertiaDeg`（局部=全局）与 `ramificationIdx_mul_inertiaDeg_eq_finrank`（乘积=finrank），给不出具体值 1；当前 FLT port 本身仍 watchdog FAIL。
- 一个可查的充分条件：若所选 place 的 residue 域与基 residue 域有显式 `≃ₐ`（`ResidueFieldEquiv` 命名输入），则 residue degree = 1；若 `F = ℚ` 且 residue 域与 `ℚ_p` 自然同构，也可得。
- 反面来源：`BadPlaceRationalDegreeFactorActual` 的 `RationalDegreeGreaterOneSource` 记录了 residue degree > 1 的具体情形；这是为什么不能无条件断言 1。

- 充分条件文件 `Mzk1C17ResidueFieldEquivActual`：**DONE 23:54:04Z（27s）**，ole 49,080B；`ResidueFieldEquiv (p) (P) := Nonempty ((S⧸P) ≃ₐ[R⧸p] R⧸p)`；`inertiaDeg'_eq_one_of_residueFieldEquiv`（PROVED conditional）由 `inertiaDeg'_algebraMap` + `LinearEquiv.finrank_eq` + `CommSemiring.finrank_self` 得出 inertiaDeg'=1。未断言实际位置存在该同构；`localResidueDegree=1` 的充分条件已可查。

#### 13.1j residueFieldEquiv ⇒ localResidueDegree=1 ⇒ weight=1 链（2026-11-13 08:05）

- 文件 `Mzk1C17ResidueWeightChainActual`：**DONE 00:04:45Z（68s）**，ole 77,008B；无 sorry/axiom。
- `localResidueDegree_eq_one_of_residueFieldEquiv`：section place 的 `ResidueFieldEquiv` ⇒ `localResidueDegree=1`（`inertiaDeg'_eq_one_of_residueFieldEquiv` 实例化）。
- `nativeBadLocalWeight_eq_one_of_residueFieldEquiv`：residue equiv + FINITE/AGREE/unramified e=1 ⇒ `nativeBadLocalWeight=1`，接 qpilot `Mzk1P3WeightDegreeOneActual` 的 GAP-PC-WEIGHT。
- 仍未断言实际 residue-field 同构；`localResidueDegree=1`/`eSource=1` 仍是 irreducible arithmetic input。

#### 13.1k AGREE 关闭 + bridge 强化（2026-11-13 19:19）

- mainline `Mzk1P3AgreeFLTActual` DONE 11:13:10Z：AGREE-RAM/AGREE-FIELD 由 FLT BaseChange :685/:721 证；`localDataAgreesWithPlaceData_of_implies` 无条件。
- `Mzk1C17UnramResidueBridgeActual` 新增 `nativeBadLocalWeight_eq_one_of_unram_residue_bridge_agree`：使用上述 AGREE 定理实例，**不再需要 hagree 假设**；文件 DONE 11:18:55Z（89s，ole 存在）。
- 现在 weight 直接条件通道只剩 FINITE + e=1 + f=1（AGREE 已关闭）。
