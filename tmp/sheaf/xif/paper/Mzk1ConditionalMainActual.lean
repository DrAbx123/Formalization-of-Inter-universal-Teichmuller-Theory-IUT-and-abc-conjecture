/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1StructuralTargetActual
import tmp.sheaf.xif.paper.Mzk1N5WeakSkeletonActual
import tmp.sheaf.xif.paper.Mzk1PerPlaceReductionActual
import tmp.sheaf.xif.paper.Mzk1QRegionInclusionActual
import tmp.sheaf.xif.paper.Mzk1ContainAttemptActual
import tmp.sheaf.xif.paper.Mzk1ThetaSectionActual
import tmp.sheaf.xif.paper.Mzk1LogMeasureSubmodularActual
import Mathlib.Tactic

/-! # A1101: conditional main assembly -/

/-
| field | value |
|---|---|
| Status | CONDITIONAL CHAIN ASSEMBLY — **not** an unconditional proof |
| 含义 | 每个定理都以其显式结构对象/假设为前提；结构对象存在性 = GAP（GAP-XID / GAP-MODPOINT / GAP-ARCH-THETA / GAP-PVAL-THETA） |
| 目标形式 | `M = A + rhs`（`rhs = -R = -|log Theta|`）；variant ⇔ `0 <= M` |
| 真证 | `variant_of_containment`; `variant_of_N5Weak0`; `variant_of_perPlace`; `variant_of_thetaSection`; `variant_of_qRegionInclusion` |
| 交叉引用 | StructuralTarget / N5WeakSkeleton / PerPlaceReduction / QRegionInclusion / ContainAttempt / ThetaSection / LogMeasureSubmodular |
| 循环性 | no target assumed; all conclusions derive from explicit data |
-/

noncomputable section
open MeasureTheory
open LeanFormal.IUT.XiFPaper.Mzk1N5WeakSkeletonActual

namespace LeanFormal.IUT.XiFPaper.Mzk1ConditionalMainActual

/-- The conditional variant value `M = A + rhs` (with `rhs = -R`). -/
def MValue (A rhs : Real) : Real := A + rhs

/-- **From a structural containment object** (QPilotThetaContainment, A1085):
`-A <= -R` gives `0 <= M = A + (-R)`. -/
theorem variant_of_containment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {A R : Real}
    (D : Mzk1StructuralTargetActual.QPilotThetaContainment Ω μ A R) :
    0 ≤ MValue A (-R) := by
  have h : -A ≤ -R := Mzk1StructuralTargetActual.target_of_containment D
  unfold MValue
  linarith

/-- **From `N5Weak A rhs 0`** (our weak N5 assumption, A1044/A1078): `0 <= M`. -/
theorem variant_of_N5Weak0 {A rhs : Real} (h : N5Weak A rhs 0) :
    0 ≤ MValue A rhs := by
  have h' := variant_of_N5Weak_zero h
  simpa [MValue, MOf] using h'

/-- **From per-place deficit data** (A1078): `0 <= M_perPlace`. -/
theorem variant_of_perPlace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V ind2 A : ι → Real} {sF : Real}
    (h : Mzk1PerPlaceReductionActual.PerPlaceDeficit V ind2 A sF) :
    0 ≤ Mzk1PerPlaceReductionActual.MOf V ind2 A sF :=
  Mzk1PerPlaceReductionActual.total_of_perPlace h

/-- **From theta-section data** (A1088): nonpositive determinant degree gives `0 <= -degree`. -/
theorem variant_of_thetaSection (D : Mzk1ThetaSectionActual.ThetaSectionData) :
    0 ≤ -D.degree := by
  have h : D.degree ≤ 0 := Mzk1ThetaSectionActual.hcmp_of_theta_section D
  linarith

/-- **From rank-one region inclusion** (A1046/A1051): thetaRegion ⊆ qRegion gives
`-A <= -R` (the QRegion coordinate convention). -/
theorem variant_of_qRegionInclusion {α : Type} [MeasurableSpace α]
    (D : Mzk1QRegionInclusionActual.QRegionData α)
    (h : D.thetaRegion ⊆ D.qRegion) :
    -D.absLogQ ≤ -D.absLogTheta :=
  Mzk1QRegionInclusionActual.variant_rankone_conditional D h

/-- Cross-reference: the scaled-containment bridge of ContainAttempt (A1061/A1069). -/
theorem variant_of_scaledContainment_shape {X : Type*} [Mul X] [MeasurableSpace X]
    {μ : Measure X} {a : X} {S : Set X}
    (h : ∀ x, x ∈ S → a * x ∈ S)
    (hS : LeanFormal.IUT.NumberFieldFinitePlace.haarLogVolume μ S ≠ ⊤) :
    Mzk1ContainAttemptActual.qLog μ S ≤ Mzk1ContainAttemptActual.qLog μ
      (Mzk1ContainAttemptActual.scaledRegion a S) :=
  Mzk1ContainAttemptActual.qLog_le_of_scaled_containment h hS

def conditionalMainRows : List (String × String) :=
  [ ("variant_of_containment", "QPilotThetaContainment -> 0 <= M (PROVED, conditional)") ,
    ("variant_of_N5Weak0", "N5Weak A rhs 0 -> 0 <= M (PROVED, conditional)") ,
    ("variant_of_perPlace", "PerPlaceDeficit -> 0 <= M_perPlace (PROVED, conditional)") ,
    ("variant_of_thetaSection", "ThetaSectionData -> 0 <= -degree (PROVED, conditional)") ,
    ("variant_of_qRegionInclusion", "thetaRegion subset qRegion -> -A <= -R (PROVED, conditional)") ,
    ("variant_of_scaledContainment_shape", "scaled containment -> qLog <= thetaLog (PROVED, conditional)") ,
    ("GAP-XID", "no inhabitant of the structural objects (Step (xi-d))") ,
    ("GAP-ARCH-THETA/GAP-PVAL-THETA", "theta-section estimate fields are hypotheses") ]

theorem conditionalMainRows_length : conditionalMainRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ConditionalMainActual