import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.C3TensorConstruction
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import Mathlib

/-!
# C7 tensorUnit actual attempt from NativeTensorLandingDonor

The native tensor landing donor carries an arbitrary tensorUnit and only the
landing equation tensorLanding_q.  This file records the exact source-version
membership target for that tensorUnit, reduces it to the q tensor landing, and
proves the tensorUnit = 1 conditional.  No arbitrary unit is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7TensorUnitActualAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3TensorConstruction
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable (L : NativeTensorLandingDonor X)

/-- Source-version tensorUnit membership in the actual canonical unit
reference of the native tensor block. -/
def NativeTensorUnitMembership : Prop :=
  (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) ∈
    arithmeticTupleCanonicalUnitReference L.tensorPlaces L.tensorTuple

/-- The native tensorUnit membership is exactly the membership of the q tensor
landing, using the actual tensorLanding_q equation. -/
theorem nativeTensorUnitMembership_iff_landing_q_mem (D : NativeQDonor X) :
    NativeTensorUnitMembership (L := L) ↔
      L.tensorLanding (nativeQ X D).q ∈
        arithmeticTupleCanonicalUnitReference L.tensorPlaces L.tensorTuple := by
  unfold NativeTensorUnitMembership
  rw [← L.tensorLanding_q D]

/-- Conditional membership if the native tensor unit is 1. -/
theorem nativeTensorUnitMembership_of_eq_one
    (h : (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) = 1) :
    NativeTensorUnitMembership (L := L) := by
  unfold NativeTensorUnitMembership
  rw [h, arithmeticTupleCanonicalUnitReference_eq_integralClosure]
  exact isIntegral_one

end LeanFormal.IUT.N8Closure.C7TensorUnitActualAttempt
