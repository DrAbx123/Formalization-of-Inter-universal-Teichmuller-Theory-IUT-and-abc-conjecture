import tmp.sheaf.n8.closure.C3OverFTensorTarget
import tmp.sheaf.n8.closure.P6Tensor
import tmp.sheaf.n8.closure.C3KummerActual
import Mathlib

/-!
# Wave20: over-F corrected C3 consumer

The zero-sorry OverFC3TensorTarget is connected to a corrected C3 consumer:
actual native q/roots/Kummer data plus the over-F tensor unit and landing.

Rewiring status:

- REWIRE NOW: any consumer that only needs the C3 -> tensor output can use
  OverFCorrectedC3Consumer below; it is actual and zero-sorry.
- MUST CHANGE TARGET: frozen consumers whose field type is
  P6Tensor.P6TensorLandingData (= NativeTensorLandingDonor) or
  P6Tensor.P6C3TensorOutput still mention the Fmod tensor block.  This includes
  C3CompleteSourceObject.landing / P6 tensor field and the C9 P6SourceClosure
  tensor field.  They cannot be rewired without changing their target type;
  no free adapter from the over-F target to the frozen Fmod donor exists.
- Frozen-target residual is exactly Nonempty (NativeTensorLandingDonor X),
  recorded below; it is not used by the corrected consumer.
-/

noncomputable section

namespace ABCBridge.N8.C3OverFConsumerCorrection

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.P6Tensor
open ABCBridge.N8.C3OverFTensorTarget
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Corrected C3 consumer over F: actual native q, roots and Kummer class plus
the over-F tensor target. -/
structure OverFCorrectedC3Consumer where
  q : NumberFieldFinitePlace.FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
    nativeQActual X
  qUnit : (Completion (nativeFPlaceOverBad X))ˣ := nativeQUnitActual X
  roots : NatRootSystem (nativeQUnitAlgClosedActual X) :=
    nativeRoots X (nativeQDonorActual X)
  kummerClass : CyclotomicTower (AlgebraicClosure
    (Completion (nativeFPlaceOverBad X))) :=
    nativeKummerClass X (nativeQDonorActual X)
  tensor : OverFC3TensorTarget X := overFC3TensorTarget (X := X)
  qTensor : (overFC3TensorTarget X).tensorLanding (nativeQUnitActual X) =
    (overFC3TensorTarget X).tensorUnit :=
    (overFC3TensorTarget X).tensorLanding_actual

/-- Actual corrected C3 consumer, zero sorry. -/
noncomputable def overFCorrectedC3Consumer : OverFCorrectedC3Consumer X where
  q := nativeQActual X
  qUnit := nativeQUnitActual X
  roots := nativeRoots X (nativeQDonorActual X)
  kummerClass := nativeKummerClass X (nativeQDonorActual X)
  tensor := overFC3TensorTarget (X := X)
  qTensor := (overFC3TensorTarget X).tensorLanding_actual

/-- Corrected consumer existence, zero sorry. -/
theorem overFCorrectedC3Consumer_nonempty :
    Nonempty (OverFCorrectedC3Consumer X) :=
  ⟨overFCorrectedC3Consumer X⟩

/-- The unchanged frozen consumers still require the Fmod tensor landing
target P6TensorLandingData (= NativeTensorLandingDonor).  The corrected
consumer above does not use it. -/
def FrozenFmodTargetRequired : Prop :=
  Nonempty (P6TensorLandingData.{0, 0} X)

/-- Exact characterization of the frozen-target residual. -/
theorem frozenFmodTargetRequired_iff :
    FrozenFmodTargetRequired (X := X) ↔
      Nonempty (P6TensorLandingData.{0, 0} X) :=
  Iff.rfl

end ABCBridge.N8.C3OverFConsumerCorrection
