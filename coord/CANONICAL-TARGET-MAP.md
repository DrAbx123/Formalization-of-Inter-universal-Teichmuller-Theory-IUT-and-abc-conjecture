# CANONICAL-TARGET-MAP — 当前锁定目标链 vs 历史/旁支（2026-11-13 06:03）

依据：Mzk1Paper312StatementActual.lean（import S3137QThetaPilotLogVolumeReadingsActual）、S3136/S3135 gate、Mzk1HolomorphicHullLogVolumeReconciliationActual。

## 1. Canonical（当前锁定目标）

- S3137QThetaPilotLogVolumeReadingsActual：
  - qPilotLogVolumeReading P = -|log ‖P.line.C3.q.q‖|（GREEN）
  - thetaPilotHullLogVolumeReal C3 = log ((actualC3LogShellTensorHaar C3)(actualC3LogShellTensorRegion C3)).toReal（GREEN, raw unnormalized；hull = region）
  - qThetaPilotLogVolumeComparison C3 P（PENDING）
- Mzk1Paper312StatementActual：
  - Paper312Statement C3 P := qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3
  - iff qThetaPilotLogVolumeComparison（rfl）
  - iff -|log‖q‖| ≤ log Haar(region)
  - 下游 Mzk1SignedCor312ContractActual → Mzk1Cor312S3137AssemblyActual → S3135 条件组装
- 义务表（Mzk1HolomorphicHullLogVolumeReconciliationActual，12 行）：
  - 6 discharged：S3137 raw readings、det identities、hull adjunction(interface)、final CTheta≥−1 算术、paperGap↔qTheta bridge(N3)、conditional Cor312 assembly
  - 7 missing：paper normalization (raw Haar → paper V)、paper IQ carrier 实现、(Ob3-3) 源识别、multiradial comparison、theta raw Haar vs paper normalized V（[C3 block:Q_p] 因子与 C3-vs-D 字典）、StepXIContract linkage、exact hull V 上界（V ≤ (1/4)l(log d+log f)+C0）

## 2. 历史链（已过时，不作为 P0 依据）

S779（NonzeroLabel、zero_region_subset_old_paperRootThetaHull）→ S793（paperLeastLambdaOHull、OldUnionEqualsLeastLambdaOHull:Prop）→ S800（paperPossibleImages = rootThetaImageSet = ⋃ SignedLabel 含 j=0 的旧 hull；paperHullLog 基于它）→ S801（对 S793 hull 证 paperHullLog = paperQPilotRegionLog；PaperHullLogFormulaData；paperQPilotLogPaperOrder ≤ paperHullLog）→ S868/S874/S875/S900/S909/S915/S3128 消费者。

- 旧 S800 paperHullLog 的退化：Mzk1PaperHullZeroLabelActual（DONE 22:01:09Z）证 least hull = R*O = O_hol、paperHullLog = 0、与 q 阶数无关 —— 仅作为历史记录（引用 S779/S793）。
- 旧 S801 的 equality 是 S793 hull 的 log 相等（不是 paper 的 (s−1)A ≤ V+gap）。

## 3. 旁支（本轮 P4/qVFam 工作，仍可复用但不等于 canonical 目标）

- qVFamTensorBlock 上的 paperFaithfulThetaHull = F(c_root)·O_hol（Mzk1PaperFaithfulHullActual/P4）：正性/有限性 green；与 canonical C3 log-shell tensor region 是不同的载体（qVFam vs C3 block），无已证识别。
- Mzk1PaperTargetNormalization/Unconditional、Mzk1PaperBlockTargetActual 基于旧 S800 hull：标历史/旧口径。
- Mzk1PaperCorrectedTargetActual：已改写为 canonical P0CanonicalTarget=Paper312Statement（P0Gap=qThetaPilotLogVolumeComparison）。

## 4. 使用规则

- 任何新工作引用 paper 目标时，必须用 S3137/Mzk1Paper312StatementActual 的读数；S800/S801 只能作为历史对照。
- qVFam P4 hull 结果可以用于 qVFam 载体上的独立定理，但不得当作 canonical target 的进展。
- 报告任何“paper target 无条件”前，先对照 reconciliation 的 7 missing。

## 20. S3137 C3 carrier vs S1902 carrier（2026-11-13）

新增 `coord/C3-S1902-CARRIER-GAP.md`：字段对照与 GAP。
- C3: `C3LogShellTensorBlock := ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple` (C3LogShellTensorPacketActual:58-59)；Haar=addHaar (:96-98)；region=tensorIntegralRegion (:74-78)。
- S1902: `S1902Carrier := (b : Bad ...) → rootNormedExtension T b` (S1902:104; PaperRootExtensionProductHaar:35-36)；Haar=Measure.pi rootExtensionHaar (:39-41)；hull=rootExtensionProductImageHull (S1902:112)。
- 结论：不同载体/不同测度/不同归一化；`Mzk1HullLogVolumeFormulaActual` 的 normalizedLog formula 不能直接套 S3137 raw theta read。
- GAP：C3-S1902-INDEX/FIBER/REGION/HAAR/PAPERNORM；对应 S1902 文件自述 S342 的 completion-valued hull 不可识别。

---

## P3 GAP 定义（2026-11-13，mainline；防重复归因）

**术语**（务必区分三个不同对象）：
1. `ArithmeticQPilotBaseChange.localResidueDegree` / `localRamificationIndex`：
   **number-ring** 公式，与 `FinitePlaceCompletionDegree.relativeResidueDegree` / `relativeRamificationIndex` **rfl 相等**（同 `comap` 极大理想公式，仅命名空间不同）。
2. `FinitePlaceCompletionDegree.localInertiaDegree` / `localRamificationIndex`（:180/:187）：
   **adic completion 整数环**的 `IsLocalRing.maximalIdeal` 公式，和 (1) **不是同一对象**。
3. `localDataAgreesWithPlaceData`（AGREE）：
   (2) = (1) 的合取，即 completion 侧 = number-ring 侧。

**GAP 定义（P3）**：
- **GAP-PC-AGREE-RAM**：completion 侧 `ramificationIdx'` = relative number-ring `e`
  （Mathlib 无 adic completion 下 `ramificationIdx'` 不变性；只有 `≤` 与带 tower/flatness 条件的等式）。
- **GAP-PC-AGREE-FIELD**：completion 侧 `inertiaDeg'` = relative number-ring `f`
  （Mathlib 无 `𝒪_v/𝔪_v ≃+* 𝓞 k/v` 的 residue-field 同构）。
- **GAP-PC-FINITE**（独立）：`Module.Finite 𝒪_v 𝒪_w` for completed valuation rings，
  等价于 `IsIntegralClosure 𝒪_w 𝒪_v K_w`；文件中已证含入方向，反向缺失。
- **rfl 桥不关闭 AGREE**：它只把 RESDEG/UNRAM 的 `localResidueDegree` 措辞统一为
  `relativeResidueDegree`，故上述三条 GAP 保持不变。

来源：`tmp/sheaf/xif/paper/Mzk1P3ArithmeticRelativeBridgeActual.lean`（rfl 桥）、
`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionDegree.lean:180,187,~310`、
`coord/P3-EXACT-REDUCTION.md` §13.1。


### P3 GAP 的 FLT 直接来源（2026-11-13 补充）

AGREE-RAM/AGREE-FIELD 的正确复用来源是仓内已移植 FLT：
`tmp/external/ported/flt/FLT/DedekindDomain/Completion/BaseChange.lean`
- :685 `ramificationIdx_eq_ramificationIdx`（completion ramificationIdx = number-ring e）；
- :721 `inertiaDeg_eq_inertiaDeg`（completion inertiaDeg = number-ring f）；
base 侧 residue 同构见 `.../DedekindDomain/AdicValuation.lean:298,318`。
BADCHAR-PRIME 对任意 T 不可证（`PrimeConductorCurve` 只有 p/hp/e，无到 T 的数据链接）；
精确缺口见 `coord/P3-EXACT-REDUCTION.md` §14.1。

## 6. PaperQPilotObjectActual：条件 inhabitant 已有；剩余 packet/donor + input alignment（2026-11-13 更正）

**更正**：早先“line.C2 / logKummer / logKummer_eq 三源对象缺失”不准确。现有 tree 已有：
- `C2Actual.sourceLogKummerDataActual I C1`：实际 `SourceLogKummerData`；
- `QPilotLineActualConstruction.paperQPilotObjectActual`：从 `NativeC1PaperSource P` + donor D + strip + oneColumn 构造 `PaperQPilotObjectActual (I := P.input)`，其中 C2 用实际 C2、`logKummer := C2`、`logKummer_eq := rfl`。

本轮进一步把它实例化为无额外字段的包：
- `Mzk1PaperQPilotActualInhabitantOfPacketActual.paperQPilotObjectActualOfPacket`：
  `P + D + ind3TimesMuStrip 1 0 + sourceOneColumnActual P → PaperQPilotObjectActual (I := P.input)`；
- `Mzk1PaperQPilotStripOneColumnClosedActual`：strip/oneColumn 实际构造；
- `Mzk1PaperQPilotActualC2ClosedActual`：C2 实际构造。

因此 P 的条件 inhabitant 已存在。真正剩余：
1. `NativeC1PaperSource P` packet（实际 source 输入包）；
2. donor `D : SourcePilotRegionDonors (I := P.input)`；
3. **input alignment**：`P.input` 的 V 是 `NativePlaces P.X.S`，而 Paper312 实际 donor C3 的 V 是 `FinitePrimePlace 2 7`（`S2711I`）；直接等式未证。

`Mzk1PaperQPilotActualInputMismatchActual`/`ResidualInputsActual` 记录该对齐 GAP。

## 7. #7 actual V upper bound（2026-11-13）

- local zero：`Mzk1ExactHullVLocalZeroActual`。
- main-term nonneg：`Mzk1MainTermActualNonnegActual`（disc/cond Nat nonzero）。
- bound：`Mzk1MainTermActualBoundActual.normalizedLog_hull_le_actualMainTerm`，C0=0。
- 注意 V=normalizedLog；raw paper V 归一化字典仍为独立 GAP。

## 21. P5 root-unit conditional chain (2026-11-13)

Green P5 pieces:
- Mzk1P5LabelShiftActual: label-indexed analytic theta normalization.
- Mzk1P5QNormalizationInputActual: P5QNormalizationInput + p5_bridge_compare.
- Mzk1P5PhaseRelationActual: named phase relation data.
- Mzk1P5CJConditionActual: c_j=1 iff phase relation (field form).
- Mzk1P5PhaseDerivedActual: root_image_zpow + phase_relation.
- Mzk1P5CJDerivedActual: c_eq_one_iff theorem.
- Mzk1P5RootChoiceOrderActual: root choice order comparison.
- Mzk1P5HunitDerivedActual: thetaUnit_j=qRoot^(j^2) without hunit hypothesis.
- Mzk1P5ComparisonDerivedActual: cOfPhase + comparison_cOfPhase,
  so hcomparison is a theorem.
- Mzk1P5PhaseExponentDataActual: explicit label->phase exponent data.

Final conditional carrier: Mzk1P5FinalSummaryActual.P5NamedInputs with four
named inputs: toRoot (analytic field map), r (analytic root),
root_image : toRoot r = twoLthRootAt^l, and PhaseExponentData (phase
exponent map).  c_j and hcomparison are constructed by cOfPhase /
comparison_cOfPhase.  p5_final_comparison gives the conditional comparison
from these four inputs.

Remaining GAP (not fabricated): actual analytic-to-root place map/Kummer
identification; root image; paper label-to-phase exponent dictionary a_j/m_j.
The j=0 label is excluded by ThetaLabel (ROUTE3 8.14); no c_j=1 theorem.

End of P5 note.
### 21.1 P5 final green and acceptance

- Mzk1P5FinalSummaryActual DONE EXIT=0 2026-11-12T23:53:16; P5NamedInputs
  four inputs + bridgeOfInputs + p5_final_comparison.
- Mzk1P5PhaseExponentDataActual DONE 23:47:58.
- Mzk1P5ComparisonDerivedActual DONE 23:40:59 (cOfPhase/comparison_cOfPhase).
- coord/P5-ACCEPTANCE.md records the full theorem list, four named inputs,
  analytic-map nonconstructibility, axioms, and the internal-consistency
  check file Mzk1P5InternalConsistencyActual.lean (hypothetical NormedField on
  RootExtension; not the analytic bridge).

End of P5 acceptance note.
### 21.2 P5NamedInputs consumer interface (conditional)

P5NamedInputs is not on the canonical S3137/Paper312 log-volume path.  Its
intended consumer is the paper root-unit/CTheta dictionary:

  P5NamedInputs (toRoot, r, root_image, PhaseExponentData)
    -> bridgeOfInputs
    -> p5_final_comparison:
       toRoot(oddTheta q (i*r^j)/oddTheta q i)
         = cOfPhase_j * paperPhaseUnit_j * paperRootThetaUnit_j.

This is exactly the conditional IUT II Rem 2.5.1 root-unit comparison.  No
current canonical-gate file consumes it; wiring it into CTheta/line-bundle
would require the actual analytic toRoot/Kummer source, which is the GAP.  Until
then P5 must not be cited as canonical-target or Paper312 progress.

End of P5 interface note.