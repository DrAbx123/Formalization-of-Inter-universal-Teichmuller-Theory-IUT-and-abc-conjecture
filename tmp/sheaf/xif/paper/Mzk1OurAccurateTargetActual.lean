/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-! # A1122: OUR accurate Cor 3.12 target (no sF / j-average / level) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (scalar/measure skeleton PROVED; identification to paper |log Theta| = GAP) |
| 这是我们的陈述 | `A := paperQAbsLog l logQ = logQ/(2l)`；`R := -Real.log ((mu thetaRegion).toReal)`；`M := A - R` |
| 与 lana 关系 | **不含 sF/nC/j-average/level**；与 lana 的强版 SSIneq（`V >= (sF-1)A`）无关 |
| 真证 | `attarget_nonneg`；`RTarget_nonpos_of_one_le`；`MTarget_nonneg_of_one_le`；`our_variant_of_normalized_containment` |
| GAP | GAP-OUR-R：`RTarget` 与 paper 的 `|log Theta|`（S2717/S2807 的 theta-hull 读数）的识别：需证明 `RTarget μ θRegion = S2717ThetaHullLogVolume`（即 θRegion 是 C3 theta-hull 区域、μ 是 actualC3Haar） |
| GAP | GAP-OUR-QNORM：q 侧归一化 `(mu baseRegion).toReal = 1`（对应 `A = -log mu q`）在具体 qRegion 上未构造 |
| 循环性 | no target assumed; hypotheses are explicit data |
-/

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual

namespace LeanFormal.IUT.XiFPaper.Mzk1OurAccurateTargetActual

/-- Our scalar `A = |log q| = paperQAbsLog l logQ`. -/
def ATarget (l : PrimeGeFive) (logQ : Real) : Real := paperQAbsLog l logQ

/-- Our scalar `R = -log (mu thetaRegion)` (theta-hull log-volume magnitude). -/
def RTarget {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θRegion : Set Ω) : Real :=
  - Real.log ((μ θRegion).toReal)

/-- Our variant value `M = A - R`. -/
def MTarget (l : PrimeGeFive) (logQ : Real) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θRegion : Set Ω) : Real :=
  ATarget l logQ - RTarget μ θRegion

/-- **A >= 0** (for `logQ >= 0`). -/
theorem attarget_nonneg (l : PrimeGeFive) (logQ : Real) (hlogQ : 0 ≤ logQ) :
    0 ≤ ATarget l logQ := by
  exact mul_nonneg (le_of_lt (qNormFactor_pos l)) hlogQ

/-- **R <= 0** if the theta region has measure at least 1. -/
theorem RTarget_nonpos_of_one_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {θRegion : Set Ω} (h : 1 ≤ (μ θRegion).toReal) :
    RTarget μ θRegion ≤ 0 := by
  unfold RTarget
  have hlog : 0 ≤ Real.log ((μ θRegion).toReal) := Real.log_nonneg h
  linarith

/-- **M >= 0** from `A = ATarget` and `1 <= mu thetaRegion`. -/
theorem MTarget_nonneg_of_one_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {θRegion : Set Ω} {l : PrimeGeFive} {logQ : Real} {A : Real}
    (hA : A = ATarget l logQ) (hlogQ : 0 ≤ logQ)
    (h : 1 ≤ (μ θRegion).toReal) :
    0 ≤ A - RTarget μ θRegion := by
  rw [hA]
  have hR : RTarget μ θRegion ≤ 0 := RTarget_nonpos_of_one_le h
  have hA0 : 0 ≤ ATarget l logQ := attarget_nonneg l logQ hlogQ
  linarith

/-- **Normalized containment**: if `mu baseRegion = 1` and `baseRegion ⊆ thetaRegion`,
then `1 <= mu thetaRegion` and hence `M >= 0`. -/
theorem our_variant_of_normalized_containment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : PrimeGeFive} {logQ : Real} (hlogQ : 0 ≤ logQ)
    {baseRegion θRegion : Set Ω} (hμ : μ baseRegion = 1)
    (hsub : baseRegion ⊆ θRegion) (hθfin : μ θRegion < ⊤) :
    0 ≤ ATarget l logQ - RTarget μ θRegion := by
  have hmono : μ baseRegion ≤ μ θRegion := measure_mono hsub
  have hto : (μ baseRegion).toReal ≤ (μ θRegion).toReal :=
    ENNReal.toReal_mono hθfin.ne hmono
  have h1 : 1 ≤ (μ θRegion).toReal := by
    rw [hμ] at hto
    simpa using hto
  exact MTarget_nonneg_of_one_le (l := l) (logQ := logQ)
    (A := ATarget l logQ) rfl hlogQ h1

/-- **Bridge to the S2807 Haar form**: for `1 <= mu thetaRegion` (finite measure),
our `RTarget` is exactly `-(haarLogVolume mu thetaRegion).toReal` (the form used in
`S2807_thetaHullVolume_eq_haarRegion`). -/
theorem RTarget_eq_neg_haarLogVolume {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {θRegion : Set Ω}
    (hfin : μ θRegion < ⊤) (h1 : 1 ≤ (μ θRegion).toReal) :
    RTarget μ θRegion =
      -(LeanFormal.IUT.NumberFieldFinitePlace.haarLogVolume μ θRegion).toReal := by
  unfold RTarget
  rw [LeanFormal.IUT.NumberFieldFinitePlace.haarLogVolume_of_lt_top hfin,
      ENNReal.toReal_ofReal (Real.log_nonneg h1)]

def ourAccurateRows : List (String × String) :=
  [ ("ATarget", "paperQAbsLog l logQ = logQ/(2l)") ,
    ("RTarget", "-Real.log ((mu thetaRegion).toReal)") ,
    ("MTarget", "A - R") ,
    ("attarget_nonneg", "0 <= A (logQ >= 0) (PROVED)") ,
    ("RTarget_nonpos_of_one_le", "1 <= mu theta => R <= 0 (PROVED)") ,
    ("MTarget_nonneg_of_one_le", "0 <= A - R (PROVED)") ,
    ("our_variant_of_normalized_containment", "mu base = 1 and base subset theta => M >= 0 (PROVED)") ,
    ("RTarget_eq_neg_haarLogVolume", "RTarget = -(haarLogVolume mu theta) for 1 <= mu theta (PROVED)") ,
    ("GAP-OUR-R", "identification RTarget = S2717ThetaHullLogVolume (C3 theta-hull) missing") ,
    ("GAP-OUR-QNORM", "q-side normalization (mu qRegion).toReal = 1 not constructed") ]

theorem ourAccurateRows_length : ourAccurateRows.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1OurAccurateTargetActual