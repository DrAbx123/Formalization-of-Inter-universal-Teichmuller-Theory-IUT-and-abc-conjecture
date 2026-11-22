import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorProductDistribution
import Mathlib

/-!
# C3 tensor-landing proof attempt

The target is the actual map

  Completion nativeFPlaceOverBad -> ArithmeticTensorTupleBlock tensorPlaces tensorTuple

with tensorLanding_q.  The production tensor block is the product/tensor of
Fmod-completion packets at the tuple of Fmod places.  The native q lives in the
F-completion, and the tree has only the restriction Fmod -> F, not a map
F -> Fmod or F_completion -> Fmod_completion tensor.

This file records the exact missing source map as a donor interface and gives
one theorem-level named sorry for its existence.  No arbitrary linear map,
constant map, or free tuple is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C3TensorProof

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact source map donor: an actual F-completion-to-Fmod-tensor-block map
with the q landing equation.  This is precisely where the production tree has
no declaration. -/
structure NativeCompletionToTensorMap where
  p : Nat
  [hp : Fact p.Prime]
  tensorIndex : Type v
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type w
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime X.S.arithmetic.Fmod p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  completionToTensor : NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X) →
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  completionToTensor_q : ∀ (D : NativeQDonor X),
    completionToTensor (nativeQ X D).q =
      (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] NativeCompletionToTensorMap.hp
attribute [instance] NativeCompletionToTensorMap.tensorFintype

end LeanFormal.IUT.N8Closure.C3TensorProof
