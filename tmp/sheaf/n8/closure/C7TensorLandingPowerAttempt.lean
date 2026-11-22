import tmp.sheaf.n8.closure.C7ThetaCompletionSourceAttempt
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import Mathlib

/-!
# C7 tensorLanding power attempt

C3.tensorLanding is an arbitrary function field constrained only at q
(tensorLanding_q).  The canonical unit reference is the integral closure of Zp,
so it is closed under powers.  This file proves the power closure and reduces the
thetaCompletionActual unit-reference membership to two exact missing facts:

* tensorLanding power law;
* tensorUnit membership in the canonical unit reference.

No arbitrary map or completion is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7TensorLandingPowerAttempt

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

/-- The canonical unit reference is the integral closure, hence closed under
powers. -/
theorem canonicalUnitReference_pow_mem
    {y : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple}
    (hy : y ∈ arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)
    (m : ℕ) :
    y ^ m ∈ arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple := by
  rw [arithmeticTupleCanonicalUnitReference_eq_integralClosure] at hy ⊢
  exact IsIntegral.pow hy m

/-- The canonical unit reference contains 1. -/
theorem canonicalUnitReference_one_mem :
    (1 : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) ∈
      arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple := by
  rw [arithmeticTupleCanonicalUnitReference_eq_integralClosure]
  exact isIntegral_one

/-- Exact tensorLanding power law for the actual C3 tensor landing. -/
def TensorLandingPowerLaw : Prop :=
  ∀ (y : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place) (m : ℕ),
    C3.tensorLanding (y ^ m) = (C3.tensorLanding y) ^ m

/-- Exact tensorUnit membership in the canonical unit reference. -/
def TensorUnitCanonicalUnitReferenceMembership : Prop :=
  (C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) ∈
    arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple

/-- The actual qUnit completion's tensor landing is tensorUnit. -/
theorem tensorLanding_qUnit :
    C3.tensorLanding ((C3.qUnit : (CommonPrimeCompletion
      (K := I.initial.arithmetic.Fmod) C3.place)ˣ) :
        CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place) =
      (C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) := by
  rw [C3.qUnit_eq]
  change C3.tensorLanding (C3.q.q : CommonPrimeCompletion
    (K := I.initial.arithmetic.Fmod) C3.place) =
      (C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  exact C3.tensorLanding_q

/-- Power law plus tensorUnit membership imply the thetaCompletionActual
unit-reference membership. -/
theorem thetaCompletionActualUnitReferenceMembership_of_powerLaw
    (hpow : TensorLandingPowerLaw (C3 := C3))
    (hunit : TensorUnitCanonicalUnitReferenceMembership (C3 := C3)) :
    ThetaCompletionActualUnitReferenceMembership (C3 := C3) n := by
  intro j
  rw [thetaCompletionActual_eq_qUnit_pow]
  rw [hpow]
  rw [tensorLanding_qUnit]
  exact canonicalUnitReference_pow_mem (C3 := C3) hunit _

/-- Conditional actual-interface unit-reference membership. -/
theorem thetaCompletionUnitReferenceMembership_actual_of_powerLaw
    (hpow : TensorLandingPowerLaw (C3 := C3))
    (hunit : TensorUnitCanonicalUnitReferenceMembership (C3 := C3)) :
    ThetaCompletionUnitReferenceMembership (C3 := C3)
      (T := actualThetaInterface (I := I) C3) n :=
  thetaCompletionUnitReferenceMembership_actual (C3 := C3) (n := n)
    (thetaCompletionActualUnitReferenceMembership_of_powerLaw (C3 := C3) (n := n) hpow hunit)

end LeanFormal.IUT.N8Closure.C7TensorLandingPowerAttempt
