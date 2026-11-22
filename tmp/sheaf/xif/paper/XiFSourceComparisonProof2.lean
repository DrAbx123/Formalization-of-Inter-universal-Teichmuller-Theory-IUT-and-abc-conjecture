import tmp.sheaf.xif.paper.XiFInequalityProof2
import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.PaperQPilotLogVolume
import Mathlib.Tactic

/-!
# Second deep attempt: xi-f scalar comparison

Task-565 attempts AverageLeQMagnitude:

  P.procession.average <= |Real.log (paperQParameter C3)|

using the actual finite procession/average, q norm < 1, theta scales at least
one, card/weight data, and the C6 normalization identities.

The audit finds one exact missing analytic bound.  Everything else reduces to
actual declarations:

* paperQParameter C3 = ||C3.q.q||, positive and < 1 (actual qNorm facts);
* the signed q-pilot log is -|log q| (PaperXiFInclusion);
* the finite weighted average is bounded by any pointwise upper bound via
  WeightedValues.average_le_of_pointwise;
* the average is bounded by the hull hullVolume via
  PaperSignedHull.procession_average_le_hullVolume;
* theta scales at least one give average nonnegativity
  (PaperSignedHull.average_nonneg field; actual SignedHullNormalizationActual).

What is not derivable from these data is the q-side comparison of the theta
hull/procession values.  The exact missing analytic bound is the pointwise
(source) inequality

  forall j, P.procession.value j <= |Real.log (paperQParameter C3)|

or, as a weaker sufficient hull bound,

  P.hull.hullVolume <= |Real.log (paperQParameter C3)|.

Without that source comparison, the finite card bounds and q < 1 only prove
nonnegativity/positivity, not the xi-f upper bound.  No arbitrary inequality is
asserted; both missing bounds are named propositions/fields.

No True/PUnit/axiom/sorry is used.  WRITE-ONLY; compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace XiFSourceComparisonProof2

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFInequalityProof2

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {P : PaperSignedHull X label}
variable {C3 : SourcePilotRegionData (l := l) (V := V) I}

/-! ## 1. Actual q-side facts -/

/-- The paper q parameter is the norm of the actual completion q. -/
theorem paperQParameter_eq_norm :
    paperQParameter C3 = ‖C3.q.q‖ := rfl

theorem paperQParameter_pos' : 0 < paperQParameter C3 :=
  paperQParameter_pos C3

/-- The actual q norm is less than one. -/
theorem paperQParameter_lt_one : paperQParameter C3 < 1 := by
  rw [paperQParameter_eq_norm]
  exact ArithmeticQPilotLogVolume.qNorm_lt_one C3.q

/-- The log of the actual q norm is negative. -/
theorem paperQParameter_log_neg : Real.log (paperQParameter C3) < 0 :=
  Real.log_neg (paperQParameter_pos' (C3 := C3)) (paperQParameter_lt_one (C3 := C3))

/-- The q magnitude is the negative q log since q < 1. -/
theorem abs_log_paperQParameter :
    |Real.log (paperQParameter C3)| = -Real.log (paperQParameter C3) :=
  abs_of_neg (paperQParameter_log_neg (C3 := C3))

/-- The q magnitude is positive. -/
theorem abs_log_paperQParameter_pos :
    0 < |Real.log (paperQParameter C3)| :=
  abs_pos.mpr (paperQParameter_log_neg (C3 := C3)).ne

/-! ## 2. Actual finite-average reductions -/

/-- Pointwise source bound sufficient for AverageLeQMagnitude. -/
def PointwiseThetaScaleBound (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  forall j : label, P.procession.value j <= |Real.log (paperQParameter C3)|

/-- Hull-volume source bound sufficient for AverageLeQMagnitude. -/
def HullVolumeLeQMagnitude (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  P.hull.hullVolume <= |Real.log (paperQParameter C3)|

/-- A pointwise source bound implies the procession average bound, using the
actual weighted-average theorem and actual nonnegative weights. -/
theorem averageLeQMagnitude_of_pointwise
    (h : PointwiseThetaScaleBound (P := P) (C3 := C3)) :
    AverageLeQMagnitude (P := P) (C3 := C3) := by
  unfold PointwiseThetaScaleBound at h
  unfold AverageLeQMagnitude
  exact WeightedValues.average_le_of_pointwise P.procession P.weights_nonnegative h

/-- The actual finite average is bounded by the finite hull volume. -/
theorem procession_average_le_hullVolume' :
    P.procession.average <= P.hull.hullVolume :=
  P.procession_average_le_hullVolume

/-- A hull-volume source bound implies AverageLeQMagnitude by transitivity with
the actual finite-hull average bound. -/
theorem averageLeQMagnitude_of_hullVolume
    (h : HullVolumeLeQMagnitude (P := P) (C3 := C3)) :
    AverageLeQMagnitude (P := P) (C3 := C3) :=
  le_trans P.procession_average_le_hullVolume h

/-- The actual average is nonnegative; q magnitude is positive.  These sign
facts alone do not give the upper bound. -/
theorem average_nonneg_and_qMagnitude_pos :
    0 <= P.procession.average ∧
      0 < |Real.log (paperQParameter C3)| :=
  ⟨P.average_nonneg, abs_log_paperQParameter_pos (C3 := C3)⟩

/-! ## 3. Exact missing analytic bound -/

/-- The exact missing q-side comparison: the finite theta procession/hull value
is bounded by the actual q magnitude.  This is not a finite-average or card
identity; it is the source normalization comparison. -/
def MissingThetaQComparison : Prop :=
  HullVolumeLeQMagnitude (P := P) (C3 := C3)

/-- Alternative pointwise form of the same missing analytic bound. -/
def MissingPointwiseThetaQComparison : Prop :=
  PointwiseThetaScaleBound (P := P) (C3 := C3)

/-! ## 4. Conditional xi-f scalar comparison -/

/-- The conditional target: the exact pointwise source bound yields the missing
AverageLeQMagnitude.  No unconditional proof is asserted. -/
theorem averageLeQMagnitude_of_missingPointwise
    (h : MissingPointwiseThetaQComparison (P := P) (C3 := C3)) :
    AverageLeQMagnitude (P := P) (C3 := C3) :=
  averageLeQMagnitude_of_pointwise h

/-- The conditional target through the hull-volume bound. -/
theorem averageLeQMagnitude_of_missingHull
    (h : MissingThetaQComparison (P := P) (C3 := C3)) :
    AverageLeQMagnitude (P := P) (C3 := C3) :=
  averageLeQMagnitude_of_hullVolume h

/-- The exact remaining xi-f scalar comparison package. -/
structure AverageComparisonSource where
  missingThetaQ : MissingThetaQComparison (P := P) (C3 := C3)

/-- Conditional AverageLeQMagnitude from the exact missing source comparison. -/
theorem averageLeQMagnitude_of_source
    (S : AverageComparisonSource (P := P) (C3 := C3)) :
    AverageLeQMagnitude (P := P) (C3 := C3) :=
  averageLeQMagnitude_of_missingHull S.missingThetaQ

end XiFSourceComparisonProof2
end XiFPaper
end LeanFormal.IUT
