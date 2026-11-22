import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import tmp.sheaf.xif.paper.GlobalThetaPilotPossibleImagesActual

/-!
# Canonical arithmetic hull versus possible Theta-pilot images: audit

The canonical hull and unit reference of
FinitePlaceArithmeticTupleCanonicalHull are actual, decomposition-independent
regions on the tuple tensor block.  They are the hulls of the actual tensor
log-shell image (arithmeticTensorTupleLogRegion), not of the Theta-pilot
possible-image set.

This file proves the actual containment for the canonical generating image:

  arithmeticTensorTupleLogRegion ⊆ arithmeticTupleCanonicalHull.

The Theta-pilot possible-image set lives on the product of bad-place value
groups, not on the canonical tuple tensor block.  No actual comparison map is
supplied, so the Theta-pilot image-hull containment is an exact carrier gap,
not a theorem and not a fake inclusion.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace CanonicalHullImageAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.ABCBridge.Geometry
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImagesActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Finite ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)

/-- The actual canonical arithmetic hull contains the actual tensor log-shell
region that generates it. -/
theorem arithmeticTensorTupleLogRegion_subset_canonicalHull :
    arithmeticTensorTupleLogRegion places tuple ⊆
      arithmeticTupleCanonicalHull places tuple := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : forall j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : forall j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  rw [arithmeticTupleCanonicalHull_eq places tuple e]
  intro x hx
  refine ⟨e x, ?_, e.symm_apply_apply x⟩
  exact subset_hull (arithmeticTupleFieldLogImage places tuple e) ⟨x, hx, rfl⟩

/-- The canonical unit reference and canonical hull are actual regions on the
same tuple tensor carrier. -/
theorem arithmeticTupleCanonicalRegions_actual :
    IsCompact (arithmeticTupleCanonicalHull places tuple) ∧
      IsCompact (arithmeticTupleCanonicalUnitReference places tuple) := by
  letI := Fintype.ofFinite ι
  exact isCompact_arithmeticTupleCanonicalRegions places tuple

/-- Exact mismatch: the Theta-pilot possible-image set is on the bad-place
value-group product, while the canonical arithmetic hull is on the tuple tensor
block.  No actual comparison map is supplied. -/
structure ThetaPilotCanonicalHullCarrierGap : Prop where
  thetaImageCarrier : Prop
  canonicalHullCarrier : Prop
  imageSet : Prop
  canonicalHull : Prop
  comparisonMap : Prop
  imageHullContainment : Prop

/-- The exact missing comparison proposition. -/
def ThetaPilotCanonicalHullCarrierGapRequired : Prop :=
  Nonempty (ThetaPilotCanonicalHullCarrierGap (l := l))

end CanonicalHullImageAuditActual
end LeanFormal.IUT.XiFPaper
end
