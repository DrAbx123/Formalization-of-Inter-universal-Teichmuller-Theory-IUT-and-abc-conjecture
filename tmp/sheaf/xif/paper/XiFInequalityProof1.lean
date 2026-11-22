import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.paper.PaperXiFSpec

/-!
# Paper xi-f inequality: actual scalar formulas and exact comparison

Target: prove
  paperQPilotLogVolume C3 <= P.signedHullLogVolume
and equivalently
  paperQPilotLogVolume C3 in hullLogVolumeRay P.signedHullLogVolume.

The actual formulas used are:

* paperQPilotLogVolume C3 = -|log (paperQParameter C3)|  (source completion q),
* paperQPilotLogMagnitude C3 = |log (paperQParameter C3)|,
* P.signedHullLogVolume = -P.procession.average (PaperSignedHull normalization).

After these definitions the target is exactly the real comparison

  P.procession.average <= |log (paperQParameter C3)|.

This file proves the equivalence, the conditional implication, and the
object-scalar route. The comparison itself is not derivable from the q/hull
definitions alone: no production theorem relates the theta-packet procession
average to the actual q magnitude. It is recorded as the exact missing
comparison PaperThetaMagnitudeComparison. No toy/True/PUnit/axiom/sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace XiFInequalityProof1

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper

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

/-- The actual q-pilot scalar formula: -|log q| for the source completion q. -/
theorem paperQPilot_scalar_eq_neg_abs (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    paperQPilotLogVolume C3 = -|Real.log (paperQParameter C3)| :=
  paperQPilotLogVolume_eq_neg_abs_paperQParameter C3

/-- The actual q-pilot magnitude formula: |log q|. -/
theorem paperQPilot_magnitude_eq_abs_log
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    paperQPilotLogMagnitude C3 = |Real.log (paperQParameter C3)| := by
  unfold paperQPilotLogMagnitude
  rw [paperQPilotLogVolume_eq_neg_abs_paperQParameter]
  ring

/-- The actual signed hull formula: -average of the theta-packet procession. -/
theorem signedHull_eq_neg_average (P : PaperSignedHull X label) :
    P.signedHullLogVolume = -P.procession.average :=
  P.signedHullLogVolume_eq_neg_average

/-- Exact missing comparison: the procession average is at most the actual
q-pilot magnitude |log q|. This is the only non-definitional real comparison
needed for the paper xi-f inequality on the scalar side. -/
def PaperThetaMagnitudeComparison
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label) : Prop :=
  P.procession.average ≤ paperQPilotLogMagnitude C3

/-- The paper xi-f scalar statement is equivalent to the exact magnitude
comparison, using only the actual q/hull formulas. -/
theorem paperXiF_iff_thetaMagnitudeComparison
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label) :
    paperXiF (paperQParameter C3) P.signedHullLogVolume ↔
      PaperThetaMagnitudeComparison C3 P := by
  rw [paperXiF_iff]
  unfold paperSignedLog PaperThetaMagnitudeComparison
  rw [← paperQPilotLogVolume_eq_neg_abs_paperQParameter,
    P.signedHullLogVolume_eq_neg_average]
  unfold paperQPilotLogMagnitude
  constructor <;> intro h <;> linarith

/-- Conditional proof of the paper xi-f scalar statement from the exact
magnitude comparison. -/
theorem paperXiF_of_thetaMagnitudeComparison
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label)
    (h : PaperThetaMagnitudeComparison C3 P) :
    paperXiF (paperQParameter C3) P.signedHullLogVolume :=
  (paperXiF_iff_thetaMagnitudeComparison C3 P).mpr h

/-- Conditional proof of the signed inequality from the exact comparison. -/
theorem paperQPilot_le_signedHull_of_thetaMagnitudeComparison
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label)
    (h : PaperThetaMagnitudeComparison C3 P) :
    paperQPilotLogVolume C3 ≤ P.signedHullLogVolume := by
  rw [paperQPilotLogVolume_eq_neg_abs_paperQParameter,
    P.signedHullLogVolume_eq_neg_average]
  unfold PaperThetaMagnitudeComparison paperQPilotLogMagnitude at h
  rw [paperQPilotLogVolume_eq_neg_abs_paperQParameter] at h
  linarith

/-- The signed xi-f inequality is equivalent to the exact magnitude
comparison; the only missing real-log comparison is on the right. -/
theorem paperQPilot_le_signedHull_iff_thetaMagnitudeComparison
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label) :
    paperQPilotLogVolume C3 ≤ P.signedHullLogVolume ↔
      PaperThetaMagnitudeComparison C3 P := by
  rw [paperQPilotLogVolume_eq_neg_abs_paperQParameter,
    P.signedHullLogVolume_eq_neg_average]
  unfold PaperThetaMagnitudeComparison paperQPilotLogMagnitude
  rw [paperQPilotLogVolume_eq_neg_abs_paperQParameter]
  constructor <;> intro h <;> linarith

/-- Conditional ray membership for the actual paper q-pilot scalar. -/
theorem paperQPilot_mem_ray_of_thetaMagnitudeComparison
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label)
    (h : PaperThetaMagnitudeComparison C3 P) :
    paperQPilotLogVolume C3 ∈ hullLogVolumeRay P.signedHullLogVolume :=
  mem_hullLogVolumeRay_iff.mpr
    (paperQPilot_le_signedHull_of_thetaMagnitudeComparison C3 P h)

/-- The paper q-pilot object scalar equals the actual paper scalar. This is
the exact object/paper identification, not a definitional equality. -/
def ObjectQPilotEqPaper
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  O.qPilotLogVolume = paperQPilotLogVolume C3

/-- Conditional ray membership for the actual paper q-pilot object scalar,
given the object/paper scalar identification and the exact magnitude
comparison. -/
theorem objectQPilot_mem_ray_of_thetaMagnitudeComparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label)
    (hQ : ObjectQPilotEqPaper O C3)
    (h : PaperThetaMagnitudeComparison C3 P) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume := by
  rw [mem_hullLogVolumeRay_iff, hQ]
  exact paperQPilot_le_signedHull_of_thetaMagnitudeComparison C3 P h

/-- The exact missing comparison package: object/paper scalar identification
plus the theta magnitude comparison. No inhabitant is asserted. -/
structure NativeXiFScalarComparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label) where
  object_eq_paper : ObjectQPilotEqPaper O C3
  theta_magnitude_le_q : PaperThetaMagnitudeComparison C3 P

/-- The paper xi-f ray membership from the exact comparison package. -/
theorem objectQPilot_mem_ray_of_comparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label)
    (C : NativeXiFScalarComparison O C3 P) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  objectQPilot_mem_ray_of_thetaMagnitudeComparison O C3 P
    C.object_eq_paper C.theta_magnitude_le_q

/-- Exact remaining comparison, as a proposition: no production theorem proves
the procession average is at most the actual q magnitude. -/
theorem paperXiF_requires_thetaMagnitudeComparison
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X label) :
    paperXiF (paperQParameter C3) P.signedHullLogVolume ↔
      PaperThetaMagnitudeComparison C3 P :=
  paperXiF_iff_thetaMagnitudeComparison C3 P

end XiFInequalityProof1
end XiFPaper
end LeanFormal.IUT
end
