import tmp.sheaf.n8.closure.PaperP6SourceClosureOverF
import tmp.sheaf.n8.closure.C3OverFConsumerCorrection
import tmp.sheaf.n8.closure.P6Tensor
import Mathlib

/-!
# Wave30: paper P6 over-F tensor consumer

The zero-sorry OverFCorrectedC3Consumer is connected to the paper P6 route
tensor layer.  The corrected paper tensor layer is exactly the over-F consumer;
the corrected P6 source closure PaperP6SourceClosureOverF.OverFP6SourceClosure
has this consumer as its tensor field.

Frozen Fmod consumers are NOT adapted.  In particular:

- P6Tensor.P6C3TensorOutput D L is indexed by the frozen
  P6Tensor.P6TensorLandingData L (= NativeTensorLandingDonor);
- C9P6Closure.P6SourceClosure carries that frozen P6C3TensorOutput field;
- C3T11NamedClosure.C3CompleteSourceObject.landing is the same frozen donor.

They must undergo target correction to the over-F layer.  No free adapter from
the over-F consumer to a frozen P6C3TensorOutput / NativeTensorLandingDonor is
introduced here.
-/

noncomputable section

namespace ABCBridge.N8.PaperP6OverFConsumer

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.P6Tensor
open ABCBridge.N8.C3OverFConsumerCorrection
open LeanFormal.IUT.N8Closure.PaperP6SourceClosureOverF

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The paper P6 route tensor layer, corrected to the over-F block. -/
abbrev PaperP6OverFTensorLayer : Type :=
  OverFCorrectedC3Consumer X

/-- Actual corrected paper P6 tensor layer, zero sorry. -/
noncomputable def paperP6OverFTensorLayer : PaperP6OverFTensorLayer (X := X) :=
  overFCorrectedC3Consumer X

/-- Actual corrected tensor layer exists, zero sorry. -/
theorem paperP6OverFTensorLayer_nonempty :
    Nonempty (PaperP6OverFTensorLayer (X := X)) :=
  ⟨paperP6OverFTensorLayer (X := X)⟩

/-- Frozen Fmod paper P6 tensor consumers are indexed by the frozen landing
target.  This type is not the corrected layer. -/
def FrozenFmodPaperP6TensorConsumer
    (D : NativeQDonor X) (L : P6TensorLandingData X) : Type :=
  P6C3TensorOutput X D L

/-- Target-correction record: the corrected layer is over F; the frozen
consumer type is indexed by the Fmod landing target and must be corrected. -/
def PaperP6TensorTargetCorrection : Prop :=
  Nonempty (PaperP6OverFTensorLayer (X := X))

theorem paperP6TensorTargetCorrection_holds :
    PaperP6TensorTargetCorrection (X := X) :=
  paperP6OverFTensorLayer_nonempty (X := X)

end ABCBridge.N8.PaperP6OverFConsumer
