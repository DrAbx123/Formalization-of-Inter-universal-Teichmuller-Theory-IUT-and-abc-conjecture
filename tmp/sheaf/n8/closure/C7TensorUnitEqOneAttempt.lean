import tmp.sheaf.n8.closure.C7TensorUnitActualAttempt
import Mathlib

/-!
# C7 tensorUnit = 1 attempt

NativeTensorLandingDonor.tensorUnit is an arbitrary unit field.  The only
production relation is tensorLanding_q : tensorLanding(q(D)) = tensorUnit for
every NativeQDonor D.  This file reduces tensorUnit = 1 to the q tensor landing
being 1 and records the equality as the single named gap.  No arbitrary unit is
introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7TensorUnitEqOneAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3TensorConstruction
open LeanFormal.IUT.N8Closure.C7TensorUnitActualAttempt
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable (L : NativeTensorLandingDonor X)

/-- Source-version tensorUnit = 1. -/
def NativeTensorUnitEqOne : Prop :=
  (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) = 1

/-- tensorUnit = 1 is exactly the q tensor landing being 1, by tensorLanding_q. -/
theorem nativeTensorUnitEqOne_iff_landing_q_eq_one (D : NativeQDonor X) :
    NativeTensorUnitEqOne (L := L) ↔
      L.tensorLanding (nativeQ X D).q = 1 := by
  unfold NativeTensorUnitEqOne
  rw [← L.tensorLanding_q D]

/-- tensorUnit = 1 gives the canonical unit-reference membership. -/
theorem nativeTensorUnitMembership_of_eqOne
    (h : NativeTensorUnitEqOne (L := L)) :
    NativeTensorUnitMembership (L := L) :=
  nativeTensorUnitMembership_of_eq_one (X := X) (L := L) h

end LeanFormal.IUT.N8Closure.C7TensorUnitEqOneAttempt
