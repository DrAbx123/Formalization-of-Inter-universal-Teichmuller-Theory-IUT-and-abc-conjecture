import tmp.sheaf.n8.closure.C7TensorUnitEqOneAttempt
import Mathlib

/-!
# C7 tensorLanding q = 1 no-go attempt

The general statement "tensorLanding(q) != 1 for every native landing donor" is
NOT provable from the frozen fields: the donor allows a constant-one landing with
tensorUnit = 1.  This file constructs that explicit counterexample (not used as
an actual source donor) and proves the conditional equivalences under injectivity
or constancy of tensorLanding.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7TensorLandingQEqOneNoGo

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3TensorConstruction
open LeanFormal.IUT.N8Closure.C7TensorUnitActualAttempt
open LeanFormal.IUT.N8Closure.C7TensorUnitEqOneAttempt
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Explicit counterexample donor: empty tensor index, constant completion
landing 1, tensorUnit 1.  This is used only to refute a universal no-go from the
frozen fields; it is not claimed to be the actual source donor. -/
noncomputable def constantOneDonor : NativeTensorLandingDonor X where
  p := 2
  hp := inferInstance
  tensorIndex := Empty
  tensorFintype := inferInstance
  tensorPlaceIndex := fun _ => Empty
  tensorPlaces := fun i => i.elim
  tensorTuple := fun i => i.elim
  tensorUnit := 1
  tensorLanding := fun _ => 1
  tensorLanding_q := fun _ => rfl

/-- The counterexample donor lands q at 1. -/
theorem constantOneDonor_landing_q (D : NativeQDonor X) :
    (constantOneDonor X).tensorLanding (nativeQ X D).q = 1 :=
  rfl

/-- The counterexample donor has tensorUnit = 1. -/
theorem constantOneDonor_tensorUnit :
    ((constantOneDonor X).tensorUnit :
      ArithmeticTensorTupleBlock (constantOneDonor X).tensorPlaces
        (constantOneDonor X).tensorTuple) = 1 :=
  rfl

/-- The universal no-go "tensorLanding(q) != 1 for all donors" is false. -/
theorem general_tensorLanding_q_ne_one_noGo_false :
    ¬ (∀ (L : NativeTensorLandingDonor.{0, 0} X) (D : NativeQDonor X),
        L.tensorLanding (nativeQ X D).q ≠ 1) := by
  intro h
  exact h (constantOneDonor X) (nativeQDonorActual X) (constantOneDonor_landing_q X (nativeQDonorActual X))

/-- Under constancy of tensorLanding, landing q = 1 is equivalent to the constant
being 1.  The constancy is an explicit hypothesis, not an arbitrary global
assertion. -/
theorem tensorLanding_q_eq_one_iff_of_const
    (L : NativeTensorLandingDonor X)
    (c : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple)
    (hconst : ∀ y, L.tensorLanding y = c) (D : NativeQDonor X) :
    L.tensorLanding (nativeQ X D).q = 1 ↔ c = 1 := by
  rw [hconst]

/-- Under injectivity plus the actual value tensorLanding(1) = 1, landing q = 1
is equivalent to q = 1. -/
theorem tensorLanding_q_eq_one_iff_of_injective
    (L : NativeTensorLandingDonor X)
    (hinj : Function.Injective L.tensorLanding)
    (hone : L.tensorLanding (1 : NumberFieldFinitePlace.Completion
      (nativeFPlaceOverBad X)) = 1) (D : NativeQDonor X) :
    L.tensorLanding (nativeQ X D).q = 1 ↔ (nativeQ X D).q = 1 := by
  constructor
  · intro h
    apply hinj
    rw [h, hone]
  · intro h
    rw [h]
    exact hone

end LeanFormal.IUT.N8Closure.C7TensorLandingQEqOneNoGo
