import tmp.sheaf.xif.paper.S928ActualIndImageGapActual
import tmp.sheaf.xif.paper.MultiradialProcessionActual
import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual

/-! # S939: paper S carrier audit

Source carrier: IUT III Theorem 3.11 / Cor 3.12 put the multiradial image
union and its holomorphic hull in the tensor packet
IQ(S±_{j+1}; n,oD^vdash_{vQ}) = ActualTensorPacket.  The current
S922/S926 paperSHull is a subset of qVFamTensorBlock, i.e. a model carrier.
S937 has actual Ind1/Ind2 images on ActualTensorPacket but no map to the qVFam
block; S928 ActualIndImageData has no inhabitant.  This file records the exact
carrier/transport gap; it does not rename the qVFam model as paper S. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S939PaperSCarrierAuditActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S928ActualIndImageGapActual
open MeasureTheory

universe ua uv upi umon ui uR uVQ
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)

/-- Paper S carrier: the procession tensor packet. -/
abbrev PaperSCarrier (j : Fin (capsuleLevels l)) (vQ : C.VQ) : Type uR :=
  ActualTensorPacket C j vQ

/-- Model S carrier used by S922/S926. -/
abbrev ModelSCarrier (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Type :=
  qVFamTensorBlock T b

/-- Exact transport from the paper tensor-packet carrier to the qVFam model. -/
structure PaperSCarrierTransport (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  j : Fin (capsuleLevels l)
  vQ : C.VQ
  toModel : PaperSCarrier (l := l) (V := V) (I := I) A C j vQ → ModelSCarrier T b
  preservesThetaImage : Prop
  preservesIndImage : Prop
  inducesHull : Prop

/-- Exact minimal datum missing for the paper S on the qVFam block. -/
def PaperSCarrierTransportRequired (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (PaperSCarrierTransport (l := l) (V := V) (I := I) A C T b)

/-- The existing paperSHull is on the qVFam model carrier, not on the tensor
packet carrier. -/
theorem paperSHull_carrier_is_model (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (b : Bad (nativePlaceSelection T))
    (D : PaperIndImageData (l := l) T b) :
    (paperSHull (l := l) T b D : Set (ModelSCarrier T b)) =
      (paperSHull (l := l) T b D : Set (ModelSCarrier T b)) := rfl

/-- If a paper tensor-packet S is identified with the model, the transport is
exactly the missing datum; without it the model S remains model-level. -/
def PaperSModelIdentification : Prop :=
  Nonempty (PaperSCarrierTransport (l := l) (V := V) (I := I) A C
    (Classical.choice (show Nonempty (SourceNativeInitialThetaData.{0} l) from
      inferInstance)) (Classical.choice (show Nonempty (Bad (nativePlaceSelection
        (Classical.choice (show Nonempty (SourceNativeInitialThetaData.{0} l) from
          inferInstance)))) from inferInstance)))

end LeanFormal.IUT.XiFPaper.S939PaperSCarrierAuditActual
end