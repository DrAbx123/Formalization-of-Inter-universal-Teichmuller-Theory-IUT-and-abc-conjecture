import tmp.sheaf.n8.closure.C7CanonicalUnitHullInclusionAttempt
import tmp.sheaf.n8.closure.C7ThetaContainmentAttempt
import tmp.sheaf.n8.closure.T11Actual
import Mathlib

/-!
# C7 theta unit/hull final

The actual T11 interface thetaIQInterfaceActual has thetaCompletion built from
C3.qUnit and the gaussian exponent.  This file constructs the actual-interface
thetaUnitHullDonor conditionally on the exact unit-reference membership, and
proves the target correction: the unit-reference donor is sufficient for the
paper C7 theta-image containment, whose corrected target is
ThetaImageContainmentDonor (no tensorUnit search is used here).

The actual unit-reference membership remains the single named gap.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7ThetaUnitHullFinal

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Native
open ABCBridge.N8.T11Actual
open LeanFormal.IUT.N8Closure.C7CanonicalUnitHullInclusionAttempt
open LeanFormal.IUT.N8Closure.C7ThetaContainmentAttempt

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- The actual T11 interface built from C3.qUnit. -/
abbrev actualThetaInterface : SourceThetaIQInterface (I := I) C3 :=
  thetaIQInterfaceActual (I := I) C3

/-- Exact unit-reference membership for the actual qUnit theta completion. -/
def ActualThetaUnitMembership : Prop :=
  ∀ j : SignedLabel l.value,
    C3.tensorLanding (thetaCompletionActual (I := I) C3 n j) ∈
      arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple

/-- The actual thetaUnitHullDonor at the actual interface is exactly the
unit-reference membership, because the unit-reference to hull inclusion is
already actual. -/
theorem thetaUnitHullDonor_actual_iff :
    ThetaUnitHullDonor (C3 := C3) (T := actualThetaInterface (I := I) C3) n ↔
      ActualThetaUnitMembership (C3 := C3) n := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, arithmeticTupleCanonicalUnitReference_subset_canonicalHull
      C3.tensorPlaces C3.tensorTuple⟩

/-- Target correction: the unit donor is sufficient for the paper C7
theta-image containment.  The corrected weaker target is
ThetaImageContainmentDonor; no tensorUnit facts are used. -/
theorem thetaImageContainmentDonor_actual_of_unitDonor
    (h : ThetaUnitHullDonor (C3 := C3) (T := actualThetaInterface (I := I) C3) n) :
    ThetaImageContainmentDonor (C3 := C3) (actualThetaInterface (I := I) C3) n :=
  thetaImageContainmentDonor_of_unitDonor (C3 := C3) (T := actualThetaInterface (I := I) C3)
    (n := n) h

end LeanFormal.IUT.N8Closure.C7ThetaUnitHullFinal
