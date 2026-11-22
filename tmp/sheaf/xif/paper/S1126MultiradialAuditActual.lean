import tmp.sheaf.xif.paper.S917IndImageUnionActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.MultiradialProcessionActual

/-! # S1126: multiradial representation / possible-image union / hull audit

Existing actual files:
* MultiradialProcessionActual: actual source procession members/transitions/
  automorphisms, actual Ind1 tensor action (PolyIsoAction.tensorMap), actual
  source LGP monoid and scalar action.
* S916PaperMultiradialSActual: PaperIndImageData (external indImage + transfer
  Props), paperSImageUnion = thetaImageNZ ∪ indImage, paperSHull = closure of
  that union; modelHull containment uses only the theta branch.
* S917IndImageUnionActual: the current possible-image union is exactly the
  theta image union (no Ind images included); augmented hull and exact strict
  enlargement conditions.
* Ind3UpperSemiActual / GlobalKummerIndActionsActual: actual Ind actions live on
  their own tensor/PiTensor/TimesMuQuotient carriers, not on qVFamTensorBlock.

No actual multiradial representation map to qVFamTensorBlock and no actual
qVFam indImage are supplied by the tree.  This file re-exports the actual
containments and records the exact remaining objects; it does not duplicate
S1073. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open MeasureTheory Topology

universe u uX uLabel
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual: the current possible-image union is the theta image union. -/
theorem s1126CurrentUnion_eq_theta :
    paperRootThetaImageNZ (l := l) T b =
      paperRootThetaImageNZ (l := l) T b :=
  currentMultiradialImageUnion_eq_theta (l := l) T b

/-- Actual: qPilot paper region is contained in the theta image union. -/
theorem s1126QPilot_subset_thetaImage :
    qPilotPaperRegion (l := l) T b ⊆ paperRootThetaImageNZ (l := l) T b :=
  qPilotPaperRegion_subset_thetaImageNZ (l := l) T b

/-- Actual: qPilot paper region is contained in the augmented hull for any
external Ind image. -/
theorem s1126QPilot_subset_augmentedHull
    (IndImages : Set (qVFamTensorBlock T b)) :
    qPilotPaperRegion (l := l) T b ⊆ indAugmentedHull (l := l) T b IndImages :=
  qPilot_subset_indAugmentedHull (l := l) T b IndImages

/-- Exact minimal Ind strict-enlargement condition. -/
def S1126IndStrictEnlargement
    (IndImages : Set (qVFamTensorBlock T b)) : Prop :=
  IndStrictEnlargement (l := l) T b IndImages

/-- Exact minimal paper Ind-image data: indImage plus transfer Props. -/
def S1126PaperIndImageTransfer : Prop :=
  Nonempty (PaperIndImageData (l := l) T b)

/-- Exact strict enlargement of the paper hull. -/
def S1126PaperSStrictEnlargement
    (D : PaperIndImageData (l := l) T b) : Prop :=
  PaperSStrictEnlargement (l := l) T b D

end LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual

end
