import tmp.sheaf.xif.paper.S972IndAdditiveEmbeddingConditionsActual
import tmp.sheaf.xif.paper.S928ActualIndImageGapActual
import tmp.sheaf.xif.paper.S963ActualToBlockProjectionActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S977ActualIndImageDataFromEmbeddingsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S940Ind3ImageActual
open LeanFormal.IUT.XiFPaper.S951ActualIndImageTransferActual
open LeanFormal.IUT.XiFPaper.S963ActualToBlockProjectionActual
open LeanFormal.IUT.XiFPaper.S969IndCarrierEmbeddingActual
open LeanFormal.IUT.XiFPaper.S972IndAdditiveEmbeddingConditionsActual
open LeanFormal.IUT.XiFPaper.S928ActualIndImageGapActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe ua uv upi ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- S972 conditions yield nonempty S928 ActualIndImageData.  No empty image is
used: the construction goes through the actual S940/S951 image sources. -/
theorem s928ActualIndImageData_nonempty_of_embeddings
    (h : S972IndAdditiveEmbeddingRequired (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b)) :
    Nonempty (ActualIndImageData (l := l) T b) := by
  rcases h with ⟨j, vQ, P, f, v, m, g, ⟨E⟩⟩
  exact actualIndImageDataOfTransfer_nonempty (l := l) (V := V) (I := I)
    (A := A) (C := C) (T := T) (b := b)
    ⟨j, vQ, P, f, v, m, g,
      ⟨s963TransferOfProjections (l := l) (V := V) (I := I)
        (A := A) (C := C) (T := T) (b := b)
        (s969ProjectionTriple_of_embeddings (l := l) (V := V) (I := I)
          (A := A) (C := C) (T := T) (b := b)
          (s972EmbeddingData_of_conditions (l := l) (V := V) (I := I)
            (A := A) (C := C) (T := T) (b := b) E))⟩⟩

/-- Exact minimal requirement: S972 additive embedding conditions. -/
def S977ExactRequirement : Prop :=
  S972IndAdditiveEmbeddingRequired (l := l) (V := V) (I := I)
    (A := A) (C := C) (T := T) (b := b)

end LeanFormal.IUT.XiFPaper.S977ActualIndImageDataFromEmbeddingsActual

end
