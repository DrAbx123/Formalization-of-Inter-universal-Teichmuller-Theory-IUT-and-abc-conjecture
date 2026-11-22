import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

/-!
# S328: literal C3 lambda-O scaled region and hull

The literal object is the actual C3 log-shell tensor region O and its actual
lambda-O scaled region.  The hull is the literal least lambda-O hull from
C3LogShellTensorHolomorphicHullActual, not a unit ball, closure, or log zero.
For nonzero lambda the least hull of lambda*O is lambda*O itself.  Compactness
and finite Haar are proved.  Positivity of the unit region's Haar is recorded
as an exact normalization gap, not faked.  No inequality is stated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S328C3LiteralLambdaOHullActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

noncomputable instance c3HullBlockMeasurableSpace :
    MeasurableSpace (HullBlock C3) := borel _

noncomputable instance c3HullBlockBorelSpace :
    BorelSpace (HullBlock C3) := ⟨rfl⟩

/-- Literal unit region O: actual tensor integral region of local log-shells. -/
noncomputable abbrev literalUnitRegion : Set (HullBlock C3) :=
  actualUnitRegion C3

/-- Literal scaled region lambda * O. -/
noncomputable abbrev literalScaledRegion (lam : HullBlock C3) :
    Set (HullBlock C3) :=
  actualScaledRegion C3 lam

/-- Literal least lambda-O hull of lambda * O. -/
noncomputable abbrev literalScaledHull (lam : HullBlock C3) :
    Set (HullBlock C3) :=
  actualHolomorphicHull C3 (literalScaledRegion C3 lam)

/-- The scaled region is contained in its literal hull. -/
theorem literalScaledRegion_subset_hull (lam : HullBlock C3) :
    literalScaledRegion C3 lam ⊆ literalScaledHull C3 lam :=
  actualRegion_subset_hull C3 (literalScaledRegion C3 lam)

/-- For nonzero lambda, lambda*O is itself the least lambda-O hull. -/
theorem literalScaledHull_eq_scaledRegion
    (lam : HullBlock C3) (hlam : lam ≠ 0) :
    literalScaledHull C3 lam = literalScaledRegion C3 lam := by
  apply Set.Subset.antisymm
  · apply actualHolomorphicHull_subset_candidate C3
    refine ⟨⟨lam, hlam, rfl⟩, ?_⟩
    exact subset_rfl
  · exact literalScaledRegion_subset_hull C3 lam

/-- The scaled region is compact for nonzero lambda: continuous image of the
compact unit region. -/
theorem literalScaledRegion_compact
    (lam : HullBlock C3) (hlam : lam ≠ 0) :
    IsCompact (literalScaledRegion C3 lam) := by
  have hcont : Continuous (fun o : HullBlock C3 => lam * o) :=
    continuous_const_mul lam
  have hset : (fun o : HullBlock C3 => lam * o) ''
        actualC3LogShellTensorRegion C3 =
      {x : HullBlock C3 | ∃ o ∈ actualUnitRegion C3, x = lam * o} := by
    ext x
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨o, by simpa [actualUnitRegion] using ho, rfl⟩
    · rintro ⟨o, ho, rfl⟩
      exact ⟨o, by simpa [actualUnitRegion] using ho, rfl⟩
  rw [literalScaledRegion, actualScaledRegion, ← hset]
  exact (actualC3LogShellTensorRegion_compact C3).image hcont

/-- The literal hull is compact for nonzero lambda. -/
theorem literalScaledHull_compact
    (lam : HullBlock C3) (hlam : lam ≠ 0) :
    IsCompact (literalScaledHull C3 lam) := by
  rw [literalScaledHull_eq_scaledRegion C3 lam hlam]
  exact literalScaledRegion_compact C3 lam hlam

/-- The literal hull has finite Haar for nonzero lambda. -/
theorem literalScaledHull_measure_lt_top
    (lam : HullBlock C3) (hlam : lam ≠ 0) :
    actualC3LogShellTensorHaar C3 (literalScaledHull C3 lam) < ⊤ :=
  (literalScaledHull_compact C3 lam hlam).measure_lt_top

/-- Exact positivity gap for the unit region.  This is the only missing input
needed for positive Haar of the literal hull; it is recorded, not faked. -/
def literalUnitRegionHaarPositivityGap : Prop :=
  0 < actualC3LogShellTensorHaar C3 (literalUnitRegion C3)

/-- Conditional positivity of the literal hull from positivity of the scaled
region.  No scaling-positivity formula is assumed or faked. -/
theorem literalScaledHull_measure_pos_of_scaledRegion_pos
    (lam : HullBlock C3) (hlam : lam ≠ 0)
    (hpos : 0 < actualC3LogShellTensorHaar C3 (literalScaledRegion C3 lam)) :
    0 < actualC3LogShellTensorHaar C3 (literalScaledHull C3 lam) := by
  simpa [literalScaledHull_eq_scaledRegion C3 lam hlam] using hpos

/-- Actual literal hull object, carrying compactness, containment and finite
Haar, with the unit-region positivity gap explicit. -/
structure C3LiteralLambdaOHullObject (lam : HullBlock C3) (hlam : lam ≠ 0) where
  unitRegion : Set (HullBlock C3)
  unitRegion_eq : unitRegion = literalUnitRegion C3
  scaledRegion : Set (HullBlock C3)
  scaledRegion_eq : scaledRegion = literalScaledRegion C3 lam
  hull : Set (HullBlock C3)
  hull_eq : hull = literalScaledHull C3 lam
  region_subset_hull : scaledRegion ⊆ hull
  hull_compact : IsCompact hull
  haar : Measure (HullBlock C3)
  haar_eq : haar = actualC3LogShellTensorHaar C3
  hull_measure_lt_top : haar hull < ⊤

/-- Actual literal hull object constructor. -/
noncomputable def c3LiteralLambdaOHullObject
    (lam : HullBlock C3) (hlam : lam ≠ 0) :
    C3LiteralLambdaOHullObject C3 lam hlam where
  unitRegion := literalUnitRegion C3
  unitRegion_eq := rfl
  scaledRegion := literalScaledRegion C3 lam
  scaledRegion_eq := rfl
  hull := literalScaledHull C3 lam
  hull_eq := rfl
  region_subset_hull := literalScaledRegion_subset_hull C3 lam
  hull_compact := literalScaledHull_compact C3 lam hlam
  haar := actualC3LogShellTensorHaar C3
  haar_eq := rfl
  hull_measure_lt_top := literalScaledHull_measure_lt_top C3 lam hlam

end LeanFormal.IUT.XiFPaper.S328C3LiteralLambdaOHullActual

end
