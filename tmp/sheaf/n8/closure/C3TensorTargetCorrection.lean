import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib

/-!
# Wave18: C3 tensor target correction

The frozen NativeTensorLandingDonor target is a tensor of Fmod-completion
factors.  The actual native q lives in the F-completion.  This file defines the
actual over-F one-factor tensor block and its canonical insertion from the
F-completion.  It then records the decisive target correction: the frozen
target is a different block, and no production comparison Fmod-tensor <->
F-tensor exists.

No arbitrary linear map or free tuple is introduced.
-/

noncomputable section

namespace ABCBridge.N8.C3TensorTargetCorrection

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The rational prime under the native F-place. -/
noncomputable def nativePrime : Nat :=
  (NumberFieldFinitePlace.completionRationalPrime (nativeFPlaceOverBad X)).val

instance nativePrimeFact : Fact (Nat.Prime (nativePrime X)) :=
  ⟨(NumberFieldFinitePlace.completionRationalPrime (nativeFPlaceOverBad X)).2⟩

/-- The native F-place as a FinitePlaceAtPrime at its own prime. -/
noncomputable def nativeFPlaceAtPrime :
    FinitePlaceAtPrime X.S.arithmetic.F (nativePrime X) :=
  ⟨nativeFPlaceOverBad X, rfl⟩

/-- The actual one-factor over-F tensor block at the native F-place. -/
abbrev overFTensorBlock : Type :=
  FinitePadicTensor (p := nativePrime X)
    (fun _ : PUnit => CommonPrimeCompletion (nativeFPlaceAtPrime X))

/-- Actual canonical insertion of the normalized F-completion into the
one-factor over-F tensor block. -/
noncomputable def overFTensorInsertion
    (z : Completion (nativeFPlaceOverBad X)) : overFTensorBlock X :=
  finitePadicTensorTprod (p := nativePrime X)
    (M := fun _ : PUnit => CommonPrimeCompletion (nativeFPlaceAtPrime X))
    (fun _ => cast (by rfl : Completion (nativeFPlaceOverBad X) =
      CommonPrimeCompletion (nativeFPlaceAtPrime X)) z)

/-- The native q-unit lands in the over-F block through the canonical insertion. -/
noncomputable def nativeQOverFTensor (D : NativeQDonor X) : overFTensorBlock X :=
  overFTensorInsertion X (nativeQUnit X D)

end ABCBridge.N8.C3TensorTargetCorrection
