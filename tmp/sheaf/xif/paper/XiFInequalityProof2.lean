import tmp.sheaf.xif.PaperXiFInclusion

/-! # Deep proof reduction for paper xi-f membership (write-only)

Task-560 attempt.  The target is

    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume.

## Reduction proved here

`hullLogVolumeRay` is definitionally `Set.Iic`, so the membership is exactly
the real inequality

    O.qPilotLogVolume <= P.signedHullLogVolume.

Using the actual formulas

* `P.signedHullLogVolume = -P.procession.average` (PaperSignedHull),
* `paperQPilotLogVolume C3 = -|log(paperQParameter C3)|` (PaperXiFInclusion),

the target is equivalent to the scalar comparison

    P.procession.average <= |log(paperQParameter C3)|,

provided the object scalar equals the actual paper q-pilot scalar:

    O.qPilotLogVolume = paperQPilotLogVolume C3.

Both remaining statements are exact source comparisons, not definitions.

No shortcut, toy data, `True`, `PUnit`, `sorry`, or axiom is used.  No
inhabitant of the missing comparison structure is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace XiFInequalityProof2

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

/-- Definitional reduction of the ray membership to the real inequality. -/
theorem mem_ray_iff_le :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume ↔
      O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  Iff.rfl

/-- The signed paper hull volume is the negative of the finite procession
average (actual PaperSignedHull field). -/
theorem signedHullLogVolume_eq_neg_average :
    P.signedHullLogVolume = -P.procession.average :=
  P.signedHullLogVolume_eq_neg_average

/-- The actual paper q-pilot scalar is `-|log(paperQParameter C3)|`. -/
theorem paperQPilot_scalar_eq_neg_abs :
    paperQPilotLogVolume C3 = -|Real.log (paperQParameter C3)| :=
  paperQPilotLogVolume_eq_neg_abs_paperQParameter C3

/-- Exact remaining scalar comparison: the finite procession average is at
most the absolute log of the actual q parameter. -/
def AverageLeQMagnitude : Prop :=
  P.procession.average ≤ |Real.log (paperQParameter C3)|

/-- The object scalar equals the actual paper q-pilot scalar. -/
def ObjectQPilotEqPaper : Prop :=
  O.qPilotLogVolume = paperQPilotLogVolume C3

/-- Assuming the object scalar equality and the scalar average comparison,
the xi-f membership follows from the actual definitions. -/
theorem qPilot_mem_ray_of_scalar_comparison
    (hQ : ObjectQPilotEqPaper (O := O) (C3 := C3))
    (hAvg : AverageLeQMagnitude (P := P) (C3 := C3)) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume := by
  rw [mem_ray_iff_le]
  rw [hQ, paperQPilot_scalar_eq_neg_abs, P.signedHullLogVolume_eq_neg_average]
  exact neg_le_neg hAvg

/-- Conversely, membership plus the object-scalar equality is exactly the
scalar average comparison. -/
theorem scalar_comparison_of_mem_ray
    (hQ : ObjectQPilotEqPaper (O := O) (C3 := C3))
    (hmem : O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume) :
    AverageLeQMagnitude (P := P) (C3 := C3) := by
  rw [mem_ray_iff_le] at hmem
  rw [hQ, paperQPilot_scalar_eq_neg_abs, P.signedHullLogVolume_eq_neg_average] at hmem
  exact neg_le_neg_iff.mp hmem

/-- The exact missing comparison package.  No inhabitant is asserted: both
fields are genuine source comparisons, not definitions. -/
structure XiFScalarComparison where
  object_eq_paper : ObjectQPilotEqPaper (O := O) (C3 := C3)
  average_le_q_magnitude : AverageLeQMagnitude (P := P) (C3 := C3)

/-- From the exact scalar comparison package, the target ray membership is
derived by the actual definitions. -/
theorem qPilot_mem_ray_of_comparison
    (C : XiFScalarComparison (O := O) (P := P) (C3 := C3)) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  qPilot_mem_ray_of_scalar_comparison C.object_eq_paper C.average_le_q_magnitude

/-- Membership iff the exact scalar comparison package (with object equality
held fixed): the only missing real comparison is `average <= |log q|`. -/
theorem mem_ray_iff_scalar_comparison
    (hQ : ObjectQPilotEqPaper (O := O) (C3 := C3)) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume ↔
      AverageLeQMagnitude (P := P) (C3 := C3) := by
  constructor
  · intro h
    exact scalar_comparison_of_mem_ray hQ h
  · intro h
    exact qPilot_mem_ray_of_scalar_comparison hQ h

end XiFInequalityProof2
end XiFPaper
end LeanFormal.IUT

end
