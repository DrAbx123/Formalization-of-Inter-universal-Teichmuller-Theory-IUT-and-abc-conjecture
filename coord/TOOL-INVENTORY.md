# 数学工具库存（2026-11-10，Lead 从仓库/Mathlib 搜出，优先复用）

> 用户指令：先参考仓库已有东西；现成工具直接用，真缺才制造。以下为当前关键阻塞点的既有工具。

## A. Haar 唯一性 / 测度级 ext（F4 b1）——Mathlib 已有！
- `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` — `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean:410`（两个测度在 C_c 上积分相同 ⇒ 测度相等）。
- `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal` — `.../RieszMarkovKakutani/NNReal.lean:74`。
- 另有 `Measure.ext_of_lintegral`（`Integral/Lebesgue/Basic.lean:570`）、`ext_of_forall_lintegral_eq`（`Measure/FiniteMeasure.lean:370`）。
- 加上 `integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport`（`MeasureTheory/Measure/Haar/Unique.lean:292`）与 `addHaarScalarFactor_eq_integral_div`（:303）即可直接组装 ν = C • μ。**abc 的 S3135HaarUniquenessScalarStep 不必制造新工具，直接复用。**

## B. Completion 环等价（hull fiber / C3 completion 比较）——repo 已有！
- `LeanFormal/IUT/Foundations/AlgebraicGeometry/LogCarrierK1K2.lean:36`: `completionIsometryEquiv : SourceCompletion place ≃+* TargetCompletion place`。
- `LeanFormal/IUT/Foundations/AlgebraicGeometry/LogUnscaledImageConsumer.lean:119`: 同名工具。
- `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedCompletion.lean:63`: `NormalizedCompletion place ≃+* Completion place`。
- `FinitePlaceCommonPrimeCompletion.lean:20,63`: `CommonPrimeCompletion := NormalizedCompletion place.val` + `≃+* NormalizedCompletion`。
- `FinitePlaceNormalizedIntegers.lean:93`: `Integers (NormalizedCompletion place) ≃+* CompletionIntegers place`。
- `FinitePlaceAdicCompletionRingEquiv.lean:13`: `AdicCompletion v.asIdeal R ≃+* Ô_v`。
- `FinitePlaceCompletionPacketLogShell.lean:16`: `commonPrimeCompletionActualRingEquiv`。
- `GoodPlaceCompletion*`/`SinglePlaceCompletions` 等。**hull 的 MissingOneColumnC3FiberComparisonData 应先尝试这些现成 equiv。**

## C. p-adic completion 范数（qpilot M2a 基域 norm）——repo/Mathlib 已有！
- `LeanFormal/IUT/ABCBridge/Geometry/RelativeCompletionFinrankReduction.lean:282`: `norm_completionMap_pow_of_finrank_eq_relativeCompletionDegree`；`:293`: `norm_algebraMap_pow_...`。
- `LeanFormal/IUT/ABCBridge/Geometry/FreyTateAnalyticInput.lean:100,115,127`: `padicNorm` 引理 + **「Mathlib 的 ℚ_[p] 范数限制到 ℚ 的像等于 padicNorm」** —— 直接用于 ‖completionMap(5:ℚ)‖=5⁻¹。
- Mathlib: `padicNorm.eq_zpow_of_nonzero`、`padicValRat` 引理，`NormedField` 范数 pow 引理。

## D. 其他可复用
- 归一化/readout: `NormalizedCompletion`, `NormalizedIntegers`, `NormalizedPrincipalIdealTransportProof.lean:16` `normalizedCompletionRingEquiv`。
- 局部 log-shell 测度/指数: `IntegralLogShellHaarIndex.lean:51` `measure_integralLogShell_eq_index_mul`（abc 已在用）。
- 单元/单位: `LogShellSaturation.integralLogShell_unitLog_generation:83`。

## 使用规则
1. 阻塞时先搜 `LeanFormal/`、`tmp/`（含 archive/snapshots）、`.lake/packages/mathlib/Mathlib/`；2. 找到就复用并在本文件登记；3. 真找不到才按 §7.5 制造通用工具，并把新工具加进本库存。
## 2026-11-10 03:10 — qpilot M2a: existing p-adic norm tools found (no new tool manufactured)

Lead directive: check repo before manufacturing.  The M2a base computation uses
only existing tools:
- LeanFormal.IUT.norm_ratCast_eq_padicNorm (FreyTateAnalyticInput.lean:128):
  || (q : Q_[p]) || = padicNorm p q.
- LeanFormal.IUT.NumberFieldFinitePlace.norm_completionMap_pow_of_finrank_eq_relativeCompletionDegree
  (RelativeCompletionFinrankReduction.lean:282) and
  norm_algebraMap_pow_of_finrank_eq_relativeCompletionDegree (:293): canonical
  completion norm transport at the actual local degree.
- Example36.concretePlace_lower_absNorm (Example36SourceLogKummerIdentification.lean:277):
  absNorm of the lower rational place = 5; concretePlace_norm_completionMap_eq
  (:297): the actual completion embedding of the concrete place is a norm isometry.
- LeanFormal.IUT.BaseScalarValuationRelation.lowerPrimeValuation
  (BaseScalarValuationRelation.lean:53): valuation of the rational scalar p in the
  lower completion.
S3133PadicNormToolsActual is PARKED (no new tool manufactured).  Consumer:
S3133M2aClosedActual (M2a closure: ||completionMap (5:Q)|| = 5^-1 =>
S3133GaussianCanonicalQNorm).


## E. 顶层 `Iut/` 库与 `tmp/local-cft-port` 库（2026-11-10 Lead 发现，均有 olean，可直接 import）

lakefile.toml 注册的 lean_lib：`LeanFormal`、**`Iut`**、`PadicField`、`Reciprocity`、`ClassFieldAxiom`、`Galois`、`Herbrand`、`Brauer`、`ContinuousKummerTheory`（后 8 个 srcDir=tmp/local-cft-port）。

### E1. `Iut`（`D:\lean\Iut/`，256 文件，205 oleans）
- 模块根 `Iut.*`：`Iut/Foundations/SourceAnabelioid*.lean`、`SourceFrobenioidSystem*.lean`、`SourceDefinition52*.lean`、`SourceFiniteStage*.lean`、`SourceFrobenioidRationalMonoidTransport.lean`、`SourceFinitePlaceMLFBase.lean`（AdicCompletion algebra instances）、`SourceCombinatorialUniversalCover.lean`、`SourceContinuousAnabelioid.lean` 等。
- 用途：anabelioid/frobenioid/orbicurve/etale-cover 的 source-level 结构——可查 R1 的 source place/transport、first-triangle 的 source objects。

### E2. `ContinuousKummerTheory`（18 oleans；`tmp/local-cft-port/continuous-kummer-theory-main/`）
- `Kummer.Basic`: `Mu`, `kummerFun`, `kummerCocycle`, **`kummerRoot (a : Kˣ) : Ωˣ`**（`HasKummerRoots.exists_pow_eq`）、`kummerRoot_pow`、`kummer : Kˣ →* ContH1 Gal(Ω/K) (Mu n Ω)`、`kummer_eq`。
- `Kummer.Values`, `Kummer.PAdic`, `Kummer.Equiv`, `Kummer.Limit`, `Kummer.ZHat`, `Hilbert90`（H¹ 消失/上边界）、`ContH1/*`。
- 用途：**canonical normalized 2l-th root supply（q_v^{1/2l}）** 的 Kummer 根构造；unit/Kummer 类。

### E3. `PadicField`（19 oleans；`tmp/local-cft-port/PadicField/`）
- `Uniformizer.lean`: `wval`, `valGen`, `v p x`, `v_mul/v_pow/v_zpow`, `uniformizer_spec`, `IsUniformizer`。
- `Norm.lean`, `FieldNorm.lean`, `Complete.lean`, `Extension.lean`, `Galois.lean`, `Tower.lean`, `Ramification.lean`, `Unramified.lean`, `MaxUnramified.lean`, `ZHat.lean`, `Integers.lean`, `Teichmuller.lean`, `Powers.lean`, `PowIndex.lean`。
- 用途：qpilot M2a/M2b（p-adic norm/uniformizer/ramification）、hull completion、F4 单位/valuation。

### E4. 其它
- `Brauer`（23 oleans）：`KummerH2`, `KummerCompat`, `ArtinPairing`, `ArtinTransfer`, `FundamentalClass`, `LocalGalois`, `Unramified`, `Invariant`, `Duality*`。
- `Reciprocity`（28）、`ClassFieldAxiom`（8，`ρ = nrm(uniformizer)^e` 等）、`Galois`（2）、`Herbrand`（3）。
- 用途：local CFT/units/norm 兼容、conjugate/local reciprocity——F4 value group、first-triangle conjugate map（C2）。

## F. 使用提醒
1. 这些库的模块名是 `Iut.*` / `ContinuousKummerTheory.*` / `PadicField.*` / `Brauer.*` 等（不是 `LeanFormal.IUT.*`），lakefile 已注册、olean 已建；从 `tmp/sheaf/xif/paper/` 文件直接 `import` 即可。
2. 具体用法先 `grep` 源文件找定理名（见上），或 `#check` 于探针文件。
3. 用到的现有工具在此登记；确实缺失才按 §7.5 制造。

## 2026-11-10 03:14 — qpilot: M2a closure reuses repo tools (PadicField library acknowledged)

Lead pointed to lakefile.toml libraries built from tmp/local-cft-port (PadicField,
ContinuousKummerTheory, Brauer, Reciprocity; oleans under .lake/build/lib/lean/
PadicField/...).  For M2a the queued closure file S3133M2aClosedActual already
uses only existing repo tools:
- LeanFormal.IUT.BaseScalarValuationRelation.lowerPrimeValuation: valuation of
  the rational scalar p in the lower completion = exp(-1);
- LeanFormal.IUT.NumberFieldFinitePlace.norm_eq_absNorm_zpow (canonical norm
  formula) + Example36.concretePlace_lower_absNorm (=5) for the canonical norm
  of (5 : Completion(lower place));
- Example36.concretePlace_norm_completionMap_eq (actual isometry) to transfer to
  the Gaussian completion, yielding S3133GaussianCanonicalQNorm.
PadicField.Uniformizer (v_mul/v_pow/nrm_lt_one_iff_v_pos/uniformizer_spec) and
PadicField.Norm/Complete are the natural further tools if the concrete file needs
a local replacement; no new tool is manufactured meanwhile.


## 2026-11-10 03:14 — 新增通用工具登记（task-58 工具制造，shehdd）

- S3140NormalizationChannelToolActual（tmp/sheaf/xif/paper/，EXIT=0 SIZE 4265；probe EXIT=0 trio 5 定理）：
  通用 normalization-channel 工具：逐点 raw reading = degree-normalized V-form + 精确 normalization factor；
  加权区域求和继承同一分解；factor=0 / 逐点 factor=0 判据。
  消费者：hull Theta-half normalization channel（raw Haar ↔ V-form）、mainline weighted regional readouts、任意 LGP/normalization 消费者。
  该工具为“现有库无通用形式”时制造；实例化数据（V-form(hull)=canonical readout、factor 的确切值/零点）仍为各 consumer 的 named exact missing。
- 既有库资产 E1–E4 已命名（不 import 进 gate）：Iut、tmp/local-cft-port 的 PadicField/Reciprocity/ClassFieldAxiom/Galois/Herbrand/Brauer/ContinuousKummerTheory；Mathlib Haar uniqueness/ext 与 repo completion ring-equiv（库存 A/B）。最终验收记录 S3140FinalAcceptanceRecordActual EXIT=0 SIZE 8254 已引用。

## 2026-11-10 03:20 — hull: completion tools reused for the uniform HDD/C3 fiber (task-62/65)
- USED (no new tool): `commonPrimeCompletionActualRingEquiv` (FinitePlaceCompletionPacketLogShell.lean:16) gives `c3FiberRingEquivActualCompletion : C3LogShellFiber C3 i ≃+* Completion (c3LogShellPlace C3 i).val`; `normalizedCompletionRingEquiv` (FinitePlaceNormalizedCompletion.lean:63) available; SHELandingActual:45 gives `oneColumnStructure.localField v = Completion v` definitionally. File tmp/sheaf/xif/paper/S3132FiberBridgeFromRepoToolsActual.lean EXIT=0 results.log:146557 -> `missingFiberComparison_iff_completionComparison`: the task-62 fiber missing is EQUIVALENT to data instantiation `MissingFiberCompletionComparison` (families of ring equivalences between rational completions and actual C3 completions).
- EXTERNAL LIB USED: `Iut/Foundations/SourceFinitePlaceMLFBase.lean:41` `Iut.ThetaFinitePlace.completionRingHom (place) : Completion (comap (k:=Q) place) →+* Completion place` (+ completionAlgebra/completionScalarTower instances :59-91). File tmp/sheaf/xif/paper/S3132FiberExternalCompletionBridgeActual.lean EXIT=0 results.log:146723: defines rationalPlaceOfC3, c3CompletionRingHom; data instantiation `ActualPlaceDataForC3` (comap_eq: all selected C3 places over ONE rational place; bij: completionRingHom bijective at each = local degree one e=f=1); constructs place-restricted `MissingFiberCompletionComparisonAt` (`fiberCompletionEquivAt_of_actualPlaceData`, `missingFiberAt_of_actualPlaceData`, plus projection `missingFiberAt_of_allPlacesData`).
- OVER-STRONGNESS of the task-38 all-v form: ring isomorphisms from the same fiber can exist only at rational places whose residue characteristic matches C3.p, so the faithful form is the place-restricted one.
- placeToMod provenance: NOT found in external libs (`grep placeToMod` over D:\lean\Iut and tmp/local-cft-port: none; also no PlaceMap/tensorPlaces in Iut sources). External Iut libs are anabelioid/frobenioid source-level (256 files), PadicField is p-adic norm/uniformizer/ramification; neither provides the source place map. So the two data fields of ActualPlaceDataForC3 remain exact missing (contract separation), but they are DATA, not missing mathematics.
- PARKED: my generic tool file tmp/sheaf/xif/paper/S3132CompletionComparisonToolActual.lean (attempt, not needed) — removed from queue, superseded by the above repo-tool reuse; not citable.

### A'. 2026-11-10 03:22 — Haar 工具精确可用形式（S3140HaarExtToolProbeActual，EXIT=0 SIZE 1887，probe #check 通过）

- 双 Haar 测度成比例（直接可用）：`Measure.isMulLeftInvariant_eq_smul` / `Measure.isAddLeftInvariant_eq_smul`
  需要 [TopologicalSpace G] [Group G/AddGroup G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G]，[μ.IsHaarMeasure]，[IsFiniteMeasureOnCompacts μ']，[μ'.IsMulLeftInvariant]；
  结论 μ' = μ'.haarScalarFactor μ • μ（IsHaarMeasure 已 extends finite-on-compacts + left-invariant）。
- 无第二可数：`Measure.measure_isHaarMeasure_eq_smul_of_isOpen`，仅需 [LocallyCompactSpace G]，
  对开集 s 有 μ' s = haarScalarFactor μ' μ • μ s。
- Riesz ext：`Measure.ext_of_integral_eq_on_compactlySupported` 需 [TopologicalSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] [μ.Regular] [ν.Regular]；
  h : ∀ f : C_c(X,ℝ), ∫ f ∂μ = ∫ f ∂ν => μ = ν（NNReal 变体同，C_c(X,ℝ≥0) 的实值积分）。
  注意 Regular 不是 IsHaarMeasure 的自动结论，需显式提供（标准 lc Borel 情形成立）。
- 标量=积分比：`haarScalarFactor_eq_integral_div`：对连续紧支 f 且 ∫ f ∂μ ≠ 0，
  haarScalarFactor μ' μ = (∫ f ∂μ') / ∫ f ∂μ。
- 结论：abc 的 S3135HaarUniquenessScalarStep 不需要新工具；直接复用（1）/（2），或用（3）+（4）。


## G. 2026-11-10 03:22 新发现（stage4/hull/lattice 复用结果，Lead 登记）

- **代数闭包根系统（mainline 2l-th root 相关）**：`LeanFormal.IUT.AlgebraicClosureRootSystem.rootSystemOfAlgClosed`（`NatRootSystem.lean:75`）——可直接构造任意元素的 NatRootSystem；`Brauer.exists_root`（`tmp/local-cft-port/Brauer/KummerH2.lean:52`：`∀{Ω}[Field Ω](n)[IsAlgClosed Ω], 0<n → ∀u, ∃c, c^n=u`）；stage4 已用它们无条件构造 q_v unit 的 alg-closure root system 与 2l-th root（`S3136LGPToolReuseRootActual`），且任意根差一个 μ₂ₗ 元素。
- **Kummer/PAdic 工具**：`ContinuousKummerTheory/Kummer/PAdic.lean`：`finiteIndex_powRange_of_isDiscreteValuationRing`、`finiteKummerQuotients_of_isDiscreteValuationRing`、`padicKummerZHatEquiv`（qpilot μ-scaling/M2 可用）；`Brauer.KummerCompat`（muIncl/muPow/H2Mu restriction）；`Brauer.Invariant`（H²(K,μₙ) ≃ ℤ/n）。
- **Local CFT（stepxi C2）**：`Reciprocity/Artin.lean:133` `PadicField.artin : Kˣ →* Gal(K^ab/K)`、`ArtinInertia/ArtinUnique/ArtinContinuous`；`Kummer/Equiv` 满射；`Brauer/ArtinPairing`；`PadicField` arithFrob/frobUr/unramifiedQuotientEquiv。stepxi 已用它们把 C2 conjugate 通道做成 `S3139C2LocalKummerCopyActual` EXIT0（5261）。
- **Haar 唯一性（abc F4(b1)）**：`Mathlib/MeasureTheory/Measure/Haar/Unique.lean` 约 :923 的 **`Measure.isAddLeftInvariant_eq_smul`**（second-countable 版本，**无需 Regular/InnerRegular**）：`[LocallyCompactSpace G] [SecondCountableTopology G] (μ' μ) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsAddLeftInvariant μ'] : μ' = haarScalarFactor μ' μ • μ` —— 直接解决 pushforward 存在性半，无需 regularity binders。
- **测度级 ext（备选）**：`Measure.ext_of_integral_eq_on_compactlySupported`（Real.lean:410，需 [LocallyCompactSpace] [μ.Regular] [ν.Regular]）；`Measure.Regular` 类在 Regular.lean:317；Haar 正则实例 `regular_haarMeasure`（Haar/Basic.lean:548）；`Regular.map` 需 Homeomorph（Regular.lean:743）。
- **completion 环等价（hull fiber）**：`commonPrimeCompletionActualRingEquiv`（FinitePlaceCompletionPacketLogShell:16）、`Iut/Foundations/SourceFinitePlaceMLFBase.lean:41` `Iut.ThetaFinitePlace.completionRingHom`（外部库）——hull 已用其把 fiber 缩为数据 `ActualPlaceDataForC3`。
- **工具再复用结论**：stage4 batch-8 已把 root system/root 存在性做成无条件 actual；qpilot M2a 可用 `Brauer.exists_root`+`padic_norm_five`；abc F4(b1) 用 `isAddLeftInvariant_eq_smul` 一行。

## F. 新库依赖监视（gate-stable，2026-11-10 03:31）

- citable 流文件（tmp/sheaf/xif/paper）中 181 个 import 新库（Iut.Foundations.* / ContinuousKummerTheory / PadicField / Reciprocity / Brauer / Galois / Herbrand / ClassFieldAxiom），属流内 citable 依赖，非 gate 依赖。
- S3140 验收 gate 不 import 任何新库：41 个直接依赖中 0 个 import 新库；gate 的 paper-local 依赖闭包内 0 个新库 import；无 gate 依赖直接 import 30 个含 Iut 的 LeanFormal bridge 模块。Iut lib: 256 files/205 oleans；local-cft libs 已 built/importable。
- 维护规则：不得把新库 import 进 gate；若未来任何 gate 相关文件新增新库 import（进入 citable closure），需 re-append gate、重新验证 41 依赖 olean freshness、重跑 axiom gate（53=50+3, zero sorryAx），并更新 FINAL ACCEPTANCE RECORD 的 gate hash pair 与 ledger。

### 2026-11-10 03:45 — hull: concrete Example 3.6 place data for the fiber spec (found + used)
- `LeanFormal/IUT/IUTII/Frobenioid/Example36PacketNumberField.lean` (namespace Example36.PacketNumberFieldConstruction): packetNumberField = GaussianField; packetFinitePlace (actual finite place over 5); packetFinitePlace_comap (comap = concreteFivePlace); packetFinitePlace_natGenerator (=5); packetFinitePlace_eq_concreteGaussianFivePlace (rfl); sourceTheater_arithmetic_Fmod_eq_packet (source theater Fmod = packetNumberField); packetFiniteCompletion = packetHeightOneSpectrum.adicCompletion packetNumberField.
- `Example36GaussianSplitPlaceArithmetic.lean`: concreteGaussianFivePlace_relativeCompletionDegree_eq_one + concreteGaussianFivePlace_completion_finrank_eq_one (both Z[i] primes over 5 have e=f=1; local degree over Q_5 is 1) — transported to packetFinitePlace in tmp/sheaf/xif/paper/S3132ConcreteGaussianPlaceSpecActual.lean (EXIT=0 results 148641): spec structure ConcreteGaussianFiberDataSpec + conditional concreteGaussianFiberRingEquiv_of_surjective; probe trio 148708-148722.
- REMAINING for concrete fiber: (i) surjectivity/dimension step (injective completionMap + finrank-one => surjective; module-structure alignment needed); (ii) tie abstract C3 c3LogShellPlace to concrete packet place (no concrete OriginalInput/C3 instantiation in tree). Pages III Prop 3.2(ii) 97-99; 3.7(ii),(v) 108-112.

## G. Watchdog 依赖新鲜度限制（2026-11-10 03:41，Lead OPS note）

- 现象：watchdog 只比较每个文件 src-vs-olean mtime，不会因为依赖（import）oleans 更新而重编消费者。因此当 registry 等依赖重建后，gate（S3140ClosureGateActual）会继续显示 fresh=True 但其 olean 实际早于依赖 olean。
- 处置：需要 force-recompile 时，touch 源文件 mtime（内容不变亦可）或追加注释后重新 append 到 tmp/xif_guarded_queue.txt；然后验证目标 olean mtime > 所有关键依赖 olean mtime（尤其 registry）才算真正 fresh。
- 验收 pin 时同时报告 src sha256 + olean sha256 + olean mtime + 关键依赖 olean mtime，避免“src 未变但依赖已变”的假 fresh。

- MANUFACTURED STEP RECIPE (task-65, proved 2026-11-10 03:52, tmp/sheaf/xif/paper/S3132CompletionMapSurjectiveActual.lean EXIT=0 149726): for a place extension of number fields, completionMap (k:=k) place is SURJECTIVE (hence bijective, with completionMap_injective) whenever Module.finrank lower upper = 1. Ingredients: completionMap_injective (Foundations/NumberField/FinitePlaceExtension.lean:82); algebraMap_instAlgebraAdicCompletion (ABCBridge/Geometry/FinitePlaceCompletionDegree.lean:98: algebraMap = completionMap under global instAlgebraAdicCompletion); moduleFinite_completionAlgebra (FinitePlaceCompletionNormTransport.lean:256); CommSemiring.finrank_self; Mathlib LinearMap.injective_iff_surjective_of_finrank_eq_finrank (LinearAlgebra/FiniteDimensional/Lemmas.lean:197). Concrete instance: packet_completionMap_surjective + concreteGaussianFiberRingEquiv_unconditional for Example 3.6 packet place.

## 2026-11-10 03:57 — lattice: two new generic tools registered (checker-verified)

- `TOOL.S3137.PI-TENSOR-PERM` — tmp/sheaf/xif/paper/S3137PiTensorPermToolActual.lean:
  `piTensorPermEquiv` (pure-tensor factor permutation along `e : ι₁ ≃ ι₂`),
  `piTensorPermEquiv_tprod`, `piTensorPermEquiv_trans`;
  `piTensorSelfPermEquiv` (same-family `(⨂ i, V) ≃ₗ (⨂ i, V)`),
  `piTensorSelfPermEquiv_tprod`, `_trans`, `_refl`, `_symm`.  Packaged from
  Mathlib `PiTensorProduct.reindex`; consumer: stepxi
  `SourceInd1ConventionIdentification` (per-automorphism linear comparison of
  polyIso relabeling vs procession reindexing).  IUT III pp.604-620 Fig I.4-I.6.
- `TOOL.S3137.BAD-INDEX-SET` — tmp/sheaf/xif/paper/S3137M1ConcreteDonorActual.lean:
  `badIndexSet T := Bad (nativePlaceSelection T)` (concrete finite type of actual
  bad places), `badIndexSet_card_eq_iff_nonempty_equiv`
  (Fintype.equivOfCardEq), M1 wiring `m1InjectionData_of_equivalence`,
  `m1PrimeMatch_of_basePlace`, `m1IndexEquivalence_of_equivalence`,
  `m1_constructible_of_equivalence_and_basePlace`; exact remaining obstruction
  `S3137M1ConcreteDonorRemaining` (bad-index equivalence + base-place equality;
  placeToMod provenance contract-separated).  Consumers: qpilot M1/mainline.
- VERIFICATION RULE (adopted): citable = EXIT=0 + ACTUAL declarations + trio/no-axiom
  probe (run tools/xif_citable_check.ps1); doc-only/comment-only files and log
  parsing are NOT evidence (see M2a doc-only 147613 retraction).

## H. `vendor/promachina/snapshots/`（宝库：另一套 promachina IUT 形式化，9457 lean 文件）

- 路径：`vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/`（另有 0d52e0fd5b53 旧 snapshot）；含自有 `.lake`（**独立 lake 工程，不能直接 import**，只能作为源码参考/复制适配）。
- 关键目录：`Iut/Stage1/`、`Iut/Stage2/`、`Iut/SourceTrace/`、`Iut/Foundations/`、`docs/papers/`、`blueprint/`。
- 已发现与本项目 paper-route 相关资产：
  - `Iut/Stage1/CorollarySchema.lean`：`Corollary312Inequality`、`Corollary312ComparisonData`、`thetaPilot`/`qPilot`（`PilotLogVolume`）、`thetaPilot_side`/`qPilot_side`/`qPilot_positive`——paper route 的 Cor 3.12 比较数据的现成模板。
  - `Iut/Stage1/IUTStage1IUTIVAlgebra.lean`（~10k+ 行）：IUT IV / GenEll 的 function-level 关系与 GenEll 形式（**paper route (c) 的最重要参考**）。
  - `Iut/Stage1/IUTStage1FrobenioidShift.lean`（~24k+ 行）：`qPilotRegion` 等。
  - `Iut/SourceTrace/Corollary312SourceGraph.lean`、`IUTIVPaperLedger.lean`：Cor 3.12 源图/IV ledger、GenEll 是显式假设的诚实记录。
  - `Iut/Stage1/IUTSourceScaffold.lean`：`Corollary312ComparisonData := ...` 的另一版本。
- 其它宝库位置：`tmp/archive_sorry_20261028/`（33 个旧 n8 closure 文件）、`tmp/sheaf/gap-exploration-20261030/snapshots/`、`external/flt-lean-recon-*/FLT/`（Haar measure/HaarChar/Padic Haar 工具，独立工程仅源码参考）、`tmp/local-cft-port/`（PadicField/Brauer/Reciprocity 等，已有 olean 可 import）、`Iut/`（本工程 Iut 库，205 oleans）、`papers/motizuki_corpus/`。
- **规则**：每批前先做 10–20 分钟 repo 寻宝（在本表列出的位置 grep 关键词/定理名），找到可复用资产就复用/适配并报告 file:line+定理名；不得声称 import vendor（独立工程）。

### 2026-11-10 04:15 — shehdd REPO SURVEY VERIFIED (vendor treasure + no-import audit)

- vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/ exists with its OWN lakefile.toml + lean-toolchain (SEPARATE lake project; source reference only, cannot import).
- Iut/Stage1/CorollarySchema.lean (7527 B) verified: PilotLogVolume/signedPilotLogVolume (lines 15-38), Corollary312Inequality (line 43), Corollary312ComparisonData (line 55), thetaPilot (63), qPilot (66), thetaPilot_side (69), qPilot_side (73), qPilot_positive (later). Paper-route Cor 3.12 comparison data template.
- Iut/Stage1/IUTStage1IUTIVAlgebra.lean (443017 B): GenEll function-level relation line 8092; explicit-hypothesis record 9883-9884 ('does not formalize GenEll; keeps the exact ...'), genEll_transfer field 9900, consumer 9919. Paper route (c) reference.
- Iut/Stage1/IUTStage1FrobenioidShift.lean (4378350 B): qPilotRegion at 19363, subset fields 19365/19440, choice-based subset lemma 19379-19381, wiring 19425/19529.
- Iut/SourceTrace/Corollary312SourceGraph.lean (36818 B): explicit sourceHypothesis premises (47, 293, 445), corollary312Acceptance (184), debate/infinitude honesty notes (116, 212). IUTIVPaperLedger.lean (16293 B) GenEll explicit-hypothesis ledger.
- Iut/Stage1/IUTSourceScaffold.lean (4189 B): alternate Corollary312ComparisonData scaffold at line 61.
- NO-IMPORT AUDIT: zero 'import Iut.(Stage1|Stage2|SourceTrace)' and zero vendor/snapshot import paths under tmp/sheaf/xif/paper; grep hits for vendor/promachina/Tau Ceti are prose honesty notes only (_S1405Probe3/S1300HDDHullDetActual/S1393XRepFiberBoundActual/S1394PsiSqZeroActual). Streams correctly treat vendor as source reference, not import.
- Rule reinforced: vendor = source reference only; cite file:line + names in records; never claim vendor imports (separate lake project; our Iut root is a DIFFERENT library).


## 2026-11-10 05:15 — lattice: PRIOR-ART inventory + INDEX.REUSE ids (§7.9)

REUSE (do not rebuild): theater family/OriginalInput SourceUnitRegionHaarDataActual:119-353; Fact prime FinitePlacePadicScalarStructure:28; heightWeightBound ThetaBoundToHeightWeight:67; V2 interface Cor312ComparisonRegionV2Actual:9/26/32; qpilot M1 names S3133M1InjectionReductionActual:55/79 + S3133M1ContractObstructionActual:56/67; stage4 unit map S3136LGPGlobalUnitsToLocalUnitsActual:48/54; concrete IQ model IQCarrierConcreteModel:193/303/315/346/358/373/386/413/431; Haar/unit-region IQCarrierHaarData:181/207/215/225/265/353 + SourceContractedSupplyRealization:219/239/253/273; F4 clause chain HunitEpsilonTransferReduction:90/103/118/141/166/188 + HullVertexConvexityAssembly:119/136/155/217/277; Card/CTheta/hull CardHullReal* + HullDeterminantLogVolumeReduction:501/536/560/569 + CardAMPLThetaBoundSupply:193; Cor312 comparison Cor312ToABCBridgeInterface:200-284 + Cor312ComparisonGapReduction:128-478 + Cor312GapDictionaryLayer:176-372.
INVENTORY FILES (checker CITABLE): S3137PriorArtConcreteModelActual, S3137PriorArtHaarActual, S3137PriorArtF4HullActual, S3137PriorArtPaperRouteActual, S3137PriorArtIQCarrierActual; INDEX.REUSE ids in S3137ReuseIdsBatchActual; corpus citation strengths in S3137CitationStrengthTableActual; endgame A/B/C/D in S3137ABCDClassificationActual.
MODEL: theater-family input CLOSED BY REUSE (tree family index-dependent/injective); V=Unit route adopted; alternate encoding RETIRED (S3137ModelTheaterPrimeStripDataActual doc record). In-model M1/M2b wired by qpilot S3133ExistingModelAdaptationActual.

## 2026-11-10 05:22 — lattice: V=Unit tree-model adaptation + paper-route reuse consumption

MODEL (V = Unit route): qpilot S3133ExistingModelAdaptationActual (CITABLE 9 decls) = OriginalInput/ImageRealization/HaarData (scaling=1) from SourceUnitRegionHaarDataActual + in-model M1 (injective place map) + in-model M2b definitional qVFam + base-unit scaling interface. Superseded: Sum-V files (S3133ModelVBasis/ModelFPrimeStrip/ModelHodgeTheater/ModelThetaPacketValue/ModelSource31Data/ModelInModelR1/ModelM2bDescent) — citable but not counted; S3133ModelTheaterFamilyActual doc-only; S3137ModelTheaterPrimeStripDataActual retired. Record: S3137TreeModelAdaptationIndexActual.
PAPER-ROUTE REUSE: (b) ThetaBoundToHeightWeight:67 heightWeightBound_of_normalizedVolumeComparison + ABCHeightWeightAdditiveBoundV2 + IQCarrierConcreteModel:413/431 (S3137PaperRouteFieldBHeightActual); (c) IQCarrierHaarData:181/207/215/265/353 + CardHullRealHaarDilationDocking:178 + HaarTranslateRealLineConsumerWiring:127-165 + Cor312ComparisonGapReduction:128-306 + GapDictionaryLayer:176-372 (S3137PaperRouteFieldCRegionActual); stage4 unit map S3136LGPGlobalUnitsToLocalUnitsActual:48/54 + Fact prime FinitePlacePadicScalarStructure:28 (S3137Stage4UnitMapReuseActual); F4(b1) reuse CardHullRealHaarDilationDocking:178 + IQCarrierHaarData:181/265 + S3135HaarUniquenessToolActual (S3137F4b1HaarReuseActual).
REMAINING: abc BaseUnit (nontrivial scaling completion scalar) for S3133TreeModelBaseUnitScaling; paper logShellPoint object + nontrivial dictionary/point bound (class B); paper q=1/5 vs model q=1 convention link (class B/C); F4(a) realified identification; stage4 unit map consumer wiring.

## 2026-11-10 05:31 — lattice: pins 14041, Option-B complete, M1 concrete donor

PINS: registry frozen 14041 (S3131FinalResidualRegistryActual EXIT0 SIZE 14041, src 4AF7EC60, olean 5991A075, checker CITABLE); shehdd single re-pin pending. Gate/acceptance re-pin values pending shehdd.
OPTION-B COMPLETE: BaseUnit interface S3133TreeModelBaseUnitScaling filled by abc S3135TreeModelBaseUnitScalingActual (EXIT0 1616; s3135_treeModelBaseUnitScaling/_baseUnit/_nontrivial; baseUnit = -1, norm one) and -1 witness S3135ModelSkeletonInterfaceActual (s3135_modelBaseUnit = -1, norm 1); S3135ModelBaseUnitActual withdrawn. Stale BaseUnit blocker removed from lattice records.
M1 CONCRETE DONOR: qpilot S3133M1ConcretePrimeMatchActual (CITABLE 5 decls): S3133ConcreteTensorIndex := Bad, refl index equiv, S3133ConcreteTensorPrime_eq_five, S3131BadTensorPrimeMatch_concrete (TensorIndexPlaceCompatibility closes on concrete donor), S3133M1ConcreteDonor {index_eq, p_eq}; remaining donor field = index identification (class C). Record S3137M1ConcreteDonorIndexActual.
MODEL-ROUTE IDS (stepxi S3139RouteModelIdsActual): model M1-discharge, Haar/CardHull consumption, residual-v3 open list (general M1, capsule-label link, M0, stage4 map, fourth-triangle arithmetic inputs, comparison/measure invariance), source-core estimates, model-route prior-art audit. (c) designated interface: Cor312ComparisonGapReduction:306 + mainline S3131Gap2ReductionReuseActual.
