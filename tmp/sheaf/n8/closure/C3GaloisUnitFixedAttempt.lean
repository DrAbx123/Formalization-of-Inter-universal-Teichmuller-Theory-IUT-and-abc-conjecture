import tmp.sheaf.n8.closure.C3SourceGaloisActionAttempt
import Mathlib

/-!
# Wave9: C3 Galois unit fixedness attempt

Target: sourceGaloisUnitAction_fixed from C3SourceGaloisActionAttempt.

The native q-unit is typed in

  (AlgebraicClosure (Completion nativeFPlaceOverBad))^x

while the actual source Galois action lives on

  (SourceAlgebraicClosure nativeFPlaceOverBad)^x
  = (AlgebraicClosure (NormalizedCompletion nativeFPlaceOverBad))^x.

NormalizedCompletion is definitionally Completion, but the AlgEquiv action's
base algebra is stated for NormalizedCompletion. The direct application type
checks by defeq, while the algebraMap fixedness rewrite needs an explicit
transport of the AlgEquiv base. No such production transport declaration is
available in the tree.

This file records the exact type-transport obligation. The named theorem is
not a free transport function; it is the proof obligation itself.
-/

noncomputable section

namespace ABCBridge.N8.C3GaloisUnitFixedAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open ABCBridge.N8.C3SourceGaloisActionAttempt
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The native q-unit transported (by the definitional closure equality) to the
source algebraic-closure unit type. -/
noncomputable def nativeUnitSource (D : NativeQDonor X) :
    (SourceAlgebraicClosure (nativeFPlaceOverBad X))ˣ :=
  nativeQUnitAlgClosed X D

/-- The exact fixedness obligation for the actual Galois unit action. The
missing ingredient is the base-AlgEquiv transport between NormalizedCompletion
and Completion, not a free transport map. -/
theorem sourceGaloisUnitAction_fixed
    (D : NativeQDonor X) (σ : SourceGaloisGroup X) :
    sourceGaloisUnitAction X σ (nativeUnitSource X D) = nativeUnitSource X D := by
  sorry

/-- Consequence: the native q-unit in the source closure is fixed by every
actual Galois automorphism, conditional on the type-transport obligation. -/
theorem sourceGaloisUnitAction_fixed_apply
    (D : NativeQDonor X) (σ : SourceGaloisGroup X) :
    sourceGaloisUnitAction X σ (nativeUnitSource X D) = nativeUnitSource X D :=
  sourceGaloisUnitAction_fixed (X := X) D σ

end ABCBridge.N8.C3GaloisUnitFixedAttempt
