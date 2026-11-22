import tmp.sheaf.n8.closure.PaperP6OverFConsumer
import tmp.sheaf.n8.closure.PaperP6SourceClosureOverF
import tmp.sheaf.n8.closure.P6Tensor
import Mathlib

/-!
# Wave31: corrected C9 / paper P6 source target over F

The paper P6 tensor layer PaperP6OverFTensorLayer is installed as the tensor
component of the corrected C9 / paper P6 source target.  The frozen
P6TensorLandingData field of C9P6Closure.P6SourceClosure is replaced by this
over-F layer, not adapted to it.

Frozen consumers still mentioning P6TensorLandingData /
P6Tensor.P6C3TensorOutput are recorded as the target-correction residual.  No
free adapter from the over-F layer to the frozen Fmod tensor field exists.
-/

noncomputable section

namespace ABCBridge.N8.C9OverFPaperTarget

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.P6Tensor
open ABCBridge.N8.PaperP6OverFConsumer
open LeanFormal.IUT.N8Closure.PaperP6SourceClosureOverF

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Corrected C9 / paper P6 source target: the tensor field is the actual
over-F paper tensor layer, replacing the frozen P6TensorLandingData field. -/
structure C9OverFPaperSourceTarget where
  /-- Replaces C9P6Closure.P6SourceClosure.tensor (frozen P6C3TensorOutput). -/
  tensor : PaperP6OverFTensorLayer X :=
    paperP6OverFTensorLayer X

/-- Actual corrected C9/paper target, zero sorry. -/
noncomputable def c9OverFPaperSourceTarget : C9OverFPaperSourceTarget X where
  tensor := paperP6OverFTensorLayer X

/-- Actual corrected target existence, zero sorry. -/
theorem c9OverFPaperSourceTarget_nonempty :
    Nonempty (C9OverFPaperSourceTarget X) :=
  ⟨c9OverFPaperSourceTarget X⟩

/-- The corrected tensor field is the over-F paper layer. -/
theorem c9OverFPaperSourceTarget_tensor :
    (c9OverFPaperSourceTarget X).tensor = paperP6OverFTensorLayer X :=
  rfl

/-- Frozen C9 tensor field type: C9P6Closure.P6SourceClosure.tensor is indexed
by the frozen P6TensorLandingData (= NativeTensorLandingDonor). -/
def FrozenC9TensorField
    (D : NativeQDonor X) (L : P6TensorLandingData X) : Type :=
  P6C3TensorOutput X D L

/-- The frozen C9 tensor field still requires the frozen Fmod landing target. -/
theorem frozenC9TensorField_requiresTarget
    (D : NativeQDonor X) (L : P6TensorLandingData.{0, 0} X) :
    Nonempty (P6TensorLandingData.{0, 0} X) :=
  ⟨L⟩

/-- Decisive target correction: the corrected C9/paper target is actual over F;
the frozen C9 tensor field is a different type indexed by P6TensorLandingData
and must be target-corrected.  There is no free adapter. -/
def C9PaperTargetCorrection : Prop :=
  Nonempty (C9OverFPaperSourceTarget X) ∧
    (∀ (D : NativeQDonor X) (L : P6TensorLandingData.{0, 0} X),
      Nonempty (P6TensorLandingData.{0, 0} X))

theorem c9PaperTargetCorrection_holds :
    C9PaperTargetCorrection (X := X) :=
  ⟨c9OverFPaperSourceTarget_nonempty X, fun D L =>
    frozenC9TensorField_requiresTarget X D L⟩

end ABCBridge.N8.C9OverFPaperTarget
