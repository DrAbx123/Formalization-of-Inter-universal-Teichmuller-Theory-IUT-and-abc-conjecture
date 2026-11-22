import tmp.sheaf.xif.paper.S916PaperMultiradialSActual

/-! # S936: actual Ind action carriers vs the qVFam Ind image

The actual Ind actions exist on their own carriers:

* Ind1: `PrcAutomorphismTensorAction` on the actual capsule tensor packet;
* Ind2: `ind2TensorEquiv` on the Pi-tensor packet;
* Ind3: `ActualInd3Data` on TimesMuQuotient stages.

None of these carriers is `qVFamTensorBlock T b`, and the tree supplies no
actual map from any Ind carrier to that block.  Therefore the `indImage` of
`PaperIndImageData` cannot be constructed from the actual Ind actions alone.
This file records the exact minimal transfer data; it does not use an empty
set as a lower bound and does not fabricate an image map.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S936IndImageTransferActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open MeasureTheory

universe u ua uv upi umon ui
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact minimal transfer data needed to turn the actual Ind actions into a
qVFam-block Ind image.  The map fields are deliberately only propositions:
the actual maps are not in the tree. -/
structure S936IndImageTransferData where
  indImage : Set (qVFamTensorBlock T b)
  ind1_transfer : Prop
  ind2_transfer : Prop
  ind3_transfer : Prop

/-- Exact transfer-gap proposition. -/
def S936IndImageTransferRequired : Prop :=
  Nonempty (S936IndImageTransferData (l := l) T b)

/-- If the exact transfer data is supplied, it fills the S916 Ind surface. -/
noncomputable def paperIndImageDataOfTransfer
    (D : S936IndImageTransferData (l := l) T b) :
    PaperIndImageData (l := l) T b where
  indImage := D.indImage
  ind1_transfer := D.ind1_transfer
  ind2_transfer := D.ind2_transfer
  ind3_transfer := D.ind3_transfer

/-- Exact minimal O-containment condition for a supplied Ind image. -/
def S936IndImageSubsetO (D : S936IndImageTransferData (l := l) T b) : Prop :=
  ∀ x : qVFamTensorBlock T b, x ∈ D.indImage → ‖x‖ ≤ 1

/-- Exact minimal required statement: a nonempty transfer datum with O-bound. -/
def S936ActualIndImageRequired : Prop :=
  ∃ D : S936IndImageTransferData (l := l) T b, S936IndImageSubsetO (l := l) T b D

end LeanFormal.IUT.XiFPaper.S936IndImageTransferActual

end
