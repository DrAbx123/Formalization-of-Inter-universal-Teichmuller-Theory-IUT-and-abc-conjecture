import tmp.sheaf.n8.closure.C3GaloisUnitFixedAttempt
import Mathlib

/-!
# Wave10: NormalizedCompletion -> Completion base transport

This file closes the Wave9 type-transport gap.

The base type equality

  (Completion place)^x = (NormalizedCompletion place)^x

is definitional (NormalizedCompletion is a def alias of Completion); the cast
below is therefore the identity transport justified by rfl, not a free
transport.  The normalized q-unit is then inserted into the actual source
algebraic closure and the actual Galois action fixes it by AlgEquiv.commutes.

No free transport map is introduced.
-/

noncomputable section

namespace ABCBridge.N8.C3NormalizedCompletionTransportAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Roots
open ABCBridge.N8.C3SourceGaloisActionAttempt
open ABCBridge.N8.C3GaloisUnitFixedAttempt
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Transport the actual native q-unit along the definitional base equality
Completion = NormalizedCompletion. -/
noncomputable def qUnitNorm (D : NativeQDonor X) :
    (NormalizedCompletion (nativeFPlaceOverBad X))ˣ :=
  cast (by rfl : (Completion (nativeFPlaceOverBad X))ˣ =
    (NormalizedCompletion (nativeFPlaceOverBad X))ˣ) (nativeQUnit X D)

/-- The actual normalized q-unit inside SourceAlgebraicClosure. -/
noncomputable def unitSourceNorm (D : NativeQDonor X) :
    (SourceAlgebraicClosure (nativeFPlaceOverBad X))ˣ :=
  unitToAlgClosed (qUnitNorm X D)

/-- The actual native q-unit and the normalized transport agree definitionally. -/
theorem nativeUnitSource_eq_unitSourceNorm (D : NativeQDonor X) :
    nativeUnitSource X D = unitSourceNorm X D := rfl

/-- The actual Galois action fixes the normalized q-unit. -/
theorem unitSourceNorm_fixed (D : NativeQDonor X) (σ : SourceGaloisGroup X) :
    sourceGaloisUnitAction X σ (unitSourceNorm X D) = unitSourceNorm X D := by
  apply Units.ext
  change (σ (algebraMap (NormalizedCompletion (nativeFPlaceOverBad X))
      (SourceAlgebraicClosure (nativeFPlaceOverBad X))
      ((qUnitNorm X D : (NormalizedCompletion (nativeFPlaceOverBad X))ˣ) :
        NormalizedCompletion (nativeFPlaceOverBad X))) :
      SourceAlgebraicClosure (nativeFPlaceOverBad X)) =
    algebraMap (NormalizedCompletion (nativeFPlaceOverBad X))
      (SourceAlgebraicClosure (nativeFPlaceOverBad X))
      ((qUnitNorm X D : (NormalizedCompletion (nativeFPlaceOverBad X))ˣ) :
        NormalizedCompletion (nativeFPlaceOverBad X))
  rw [AlgEquiv.commutes]

/-- Wave9 fixedness theorem, now proved with the definitional base transport. -/
theorem sourceGaloisUnitAction_fixed (D : NativeQDonor X)
    (σ : SourceGaloisGroup X) :
    sourceGaloisUnitAction X σ (nativeUnitSource X D) = nativeUnitSource X D := by
  rw [nativeUnitSource_eq_unitSourceNorm (X := X) D]
  exact unitSourceNorm_fixed (X := X) D σ

end ABCBridge.N8.C3NormalizedCompletionTransportAttempt
