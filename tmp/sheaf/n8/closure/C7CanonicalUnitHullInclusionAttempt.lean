import tmp.sheaf.n8.closure.C7ThetaContainmentAttempt
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import Mathlib

/-!
# C7 canonical unit-reference / hull inclusion attempt

The actual canonical unit reference is contained in the actual canonical hull:
both are decomposition pullbacks, and the product unit region is contained in
the product field hull.  This is proved here from the actual definitions.

The remaining theta donor condition is the unit-reference membership of
C3.tensorLanding (T.thetaCompletion n j), which is an independent missing fact.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7CanonicalUnitHullInclusionAttempt

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldProductHull
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Native
open LeanFormal.IUT.N8Closure.C7ThetaContainmentAttempt

universe u v w ua uv upi umon ui uL uG

section CanonicalInclusion

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota → Type w}
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)

/-- The actual canonical unit reference is contained in the actual canonical
hull.  Both are pullbacks of the corresponding product regions, and the product
unit region is contained in the product field hull. -/
theorem arithmeticTupleCanonicalUnitReference_subset_canonicalHull :
    (arithmeticTupleCanonicalUnitReference places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      arithmeticTupleCanonicalHull places tuple := by
  letI := Fintype.ofFinite iota
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e,
    arithmeticTupleCanonicalHull_eq places tuple e]
  exact Set.image_mono (unitRegion_subset_arithmeticTupleFieldHull places tuple e)

end CanonicalInclusion

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (T : SourceThetaIQInterface (I := I) C3)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- Exact remaining theta condition: the completion theta image lies in the
canonical unit reference. -/
def ThetaCompletionUnitReferenceMembership : Prop :=
  ∀ j : SignedLabel l.value,
    C3.tensorLanding (T.thetaCompletion n j) ∈
      arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple

/-- The actual unit-reference inclusion plus theta unit membership gives the
preferred thetaUnitHullDonor from C7ThetaContainmentAttempt. -/
theorem thetaUnitHullDonor_of_unitReferenceMembership
    (h : ThetaCompletionUnitReferenceMembership (C3 := C3) T n) :
    ThetaUnitHullDonor (C3 := C3) T n :=
  ⟨h, arithmeticTupleCanonicalUnitReference_subset_canonicalHull
    C3.tensorPlaces C3.tensorTuple⟩

/-- Conditional theta containment using the actual unit-reference inclusion. -/
theorem thetaImageContainmentDonor_of_unitReferenceMembership
    (h : ThetaCompletionUnitReferenceMembership (C3 := C3) T n) :
    ThetaImageContainmentDonor (C3 := C3) T n :=
  thetaImageContainmentDonor_of_unitDonor (C3 := C3) (T := T) (n := n)
    (thetaUnitHullDonor_of_unitReferenceMembership (C3 := C3) (T := T) (n := n) h)

end LeanFormal.IUT.N8Closure.C7CanonicalUnitHullInclusionAttempt
