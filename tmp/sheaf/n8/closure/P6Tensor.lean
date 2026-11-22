import tmp.sheaf.n8.closure.NativeC3

import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import Mathlib

/-!
# P6 tensor/landing data and the C3 -> tensor output interface

This file freezes the P6-facing data consumed by the C3 native q/roots chain:

- the actual native q/roots/Kummer class from NativeC3/C3KummerActual;
- the tensor/landing data, currently supplied only by the missing
  NativeTensorLandingDonor;
- the C3 -> tensor output interface recording the actual q landing.

No arbitrary tensorLanding map is introduced; the missing donor is a single
theorem-level named sorry.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6Tensor

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- P6 tensor/landing data: the actual tensor block and the completion-to-tensor
landing, with the native q landing equation. -/
abbrev P6TensorLandingData := NativeTensorLandingDonor X

/-- The C3 -> tensor output interface.  The q/roots/Kummer fields are actual
NativeC3/C3KummerActual data; the tensor landing fields are the P6 donor. -/
structure P6C3TensorOutput (D : NativeQDonor X) (L : P6TensorLandingData X) where
  /-- Actual native q candidate from the source Tate comparison. -/
  q : NumberFieldFinitePlace.FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
    nativeQ X D
  /-- Actual q landing in the tensor block. -/
  qTensor : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple :=
    L.tensorLanding (nativeQ X D).q
  /-- The q landing is the source tensor unit. -/
  qTensor_eq : L.tensorLanding (nativeQ X D).q =
    (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) :=
    L.tensorLanding_q D
  /-- Actual algebraic-closure roots from NativeC3. -/
  roots : NatRootSystem (nativeQUnitAlgClosed X D) := nativeRoots X D
  /-- Actual Kummer class tower from C3KummerActual. -/
  kummerClass : CyclotomicTower (AlgebraicClosure (NumberFieldFinitePlace.Completion
    (nativeFPlaceOverBad X))) := nativeKummerClass X D

/-- Conditional P6 output from an actual native q donor and an actual tensor
landing donor, zero sorry. -/
noncomputable def p6C3TensorOutputOfDonors
    (D : NativeQDonor X) (L : P6TensorLandingData X) :
    P6C3TensorOutput X D L where
  q := nativeQ X D
  qTensor := L.tensorLanding (nativeQ X D).q
  qTensor_eq := L.tensorLanding_q D
  roots := nativeRoots X D
  kummerClass := nativeKummerClass X D

/-- Conditional P6 output existence from the source q donor and the missing
tensor landing donor; no arbitrary map is chosen. -/
theorem p6C3TensorOutput_nonempty_of_donors
    (D : NativeQDonor X) (L : P6TensorLandingData X) :
    Nonempty (P6C3TensorOutput X D L) :=
  ⟨p6C3TensorOutputOfDonors X D L⟩

end LeanFormal.IUT.N8Closure.P6Tensor
