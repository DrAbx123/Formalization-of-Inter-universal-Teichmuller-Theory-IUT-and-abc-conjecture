import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.C3TensorTargetCorrection
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib

/-!
# Wave19: corrected over-F C3 tensor target

Following Wave18, the C3 tensor target is corrected from the frozen Fmod
tensor block to the over-F block at nativeFPlaceOverBad.

This file defines the corrected target fields (tensorPlaces, tensorTuple,
tensorUnit, tensorLanding) and constructs the actual landing and tensorUnit
from the native actual q-unit by the canonical finitePadicTensorTprod insertion.
It does not use the frozen Fmod target.
-/

noncomputable section

namespace ABCBridge.N8.C3OverFTensorTarget

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open ABCBridge.N8.C3TensorTargetCorrection
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Corrected tensor index: one factor. -/
abbrev fTensorIndex : Type := PUnit

/-- Corrected tensor places: the native F-place, at its own rational prime. -/
noncomputable def fTensorPlaces : (i : fTensorIndex) → PUnit →
    FinitePlaceAtPrime X.S.arithmetic.F (nativePrime X) :=
  fun _ _ => nativeFPlaceAtPrime X

/-- Corrected tensor tuple: the singleton tuple. -/
def fTensorTuple : (i : fTensorIndex) → PUnit :=
  fun _ => PUnit.unit

/-- The corrected over-F tensor block. -/
abbrev overFC3TensorBlock : Type :=
  FinitePadicTensor (p := nativePrime X)
    (fun _ : fTensorIndex => CommonPrimeCompletion (nativeFPlaceAtPrime X))

/-- The actual canonical landing from the F-completion to the over-F block. -/
noncomputable def overFTensorLanding
    (z : Completion (nativeFPlaceOverBad X)) : overFC3TensorBlock X :=
  finitePadicTensorTprod (p := nativePrime X)
    (M := fun _ : fTensorIndex => CommonPrimeCompletion (nativeFPlaceAtPrime X))
    (fun _ => cast (by rfl : Completion (nativeFPlaceOverBad X) =
      CommonPrimeCompletion (nativeFPlaceAtPrime X)) z)

/-- Corrected C3 tensor target over F. -/
structure OverFC3TensorTarget where
  p : Nat
  [hp : Fact p.Prime]
  tensorPlaces : (i : fTensorIndex) → PUnit → FinitePlaceAtPrime X.S.arithmetic.F p
  tensorTuple : (i : fTensorIndex) → PUnit
  tensorUnit : FinitePadicTensor (p := p)
    (fun i => CommonPrimeCompletion (tensorPlaces i (tensorTuple i)))
  tensorLanding : Completion (nativeFPlaceOverBad X) →
    FinitePadicTensor (p := p)
      (fun i => CommonPrimeCompletion (tensorPlaces i (tensorTuple i)))
  tensorLanding_actual : tensorLanding (nativeQUnitActual X : Completion
    (nativeFPlaceOverBad X)) = tensorUnit

attribute [instance] OverFC3TensorTarget.hp

/-- Actual corrected over-F target, zero sorry: tensorUnit and tensorLanding
are the canonical insertion of the native actual q-unit. -/
noncomputable def overFC3TensorTarget : OverFC3TensorTarget X where
  p := nativePrime X
  hp := nativePrimeFact X
  tensorPlaces := fTensorPlaces X
  tensorTuple := fTensorTuple
  tensorUnit := overFTensorLanding X (nativeQUnitActual X)
  tensorLanding := overFTensorLanding X
  tensorLanding_actual := rfl

/-- The corrected target is over F, not the frozen Fmod block. -/
theorem overFC3TensorTarget_places :
    (overFC3TensorTarget X).tensorPlaces PUnit.unit PUnit.unit =
      nativeFPlaceAtPrime X :=
  rfl

end ABCBridge.N8.C3OverFTensorTarget
