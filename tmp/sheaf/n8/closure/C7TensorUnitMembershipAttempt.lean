import tmp.sheaf.n8.closure.C7TensorLandingPowerAttempt
import Mathlib

/-!
# C7 tensorUnit membership attempt

C3.tensorUnit is an arbitrary unit field of the arithmetic tensor block.  The
only production relation connecting it to the tensor landing is
C3.tensorLanding_q : tensorLanding(q.q) = tensorUnit.  The canonical unit
reference is the integral closure of Zp, so membership is genuinely an
integrality condition, not a formal consequence of being a unit.

This file proves the exact tensorLanding_q reduction, a conditional membership
from tensorUnit = 1, and records the missing membership as one named gap.
No arbitrary membership or map is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7TensorUnitMembershipAttempt

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
open LeanFormal.IUT.N8Closure.C7ThetaCompletionSourceAttempt
open LeanFormal.IUT.N8Closure.C7TensorLandingPowerAttempt

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

/-- tensorUnit membership is exactly the membership of the q tensor landing. -/
theorem tensorUnit_mem_iff_tensorLanding_q_mem :
    TensorUnitCanonicalUnitReferenceMembership (C3 := C3) ↔
      C3.tensorLanding (C3.q.q : CommonPrimeCompletion
        (K := I.initial.arithmetic.Fmod) C3.place) ∈
        arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple := by
  unfold TensorUnitCanonicalUnitReferenceMembership
  rw [← C3.tensorLanding_q]

/-- Conditional membership if the actual tensor unit is 1. -/
theorem tensorUnitCanonicalUnitReferenceMembership_of_eq_one
    (h : (C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) = 1) :
    TensorUnitCanonicalUnitReferenceMembership (C3 := C3) := by
  unfold TensorUnitCanonicalUnitReferenceMembership
  rw [h]
  exact canonicalUnitReference_one_mem (C3 := C3)

/-- The named tensorUnit membership together with the tensorLanding power law
gives the actual qUnit-completion unit-reference membership. -/
theorem thetaCompletionActualUnitReferenceMembership_of_tensorUnit_and_powerLaw
    (hpow : TensorLandingPowerLaw (C3 := C3))
    (hunit : TensorUnitCanonicalUnitReferenceMembership (C3 := C3)) :
    ThetaCompletionActualUnitReferenceMembership (C3 := C3) n :=
  thetaCompletionActualUnitReferenceMembership_of_powerLaw (C3 := C3) (n := n) hpow hunit

end LeanFormal.IUT.N8Closure.C7TensorUnitMembershipAttempt
