import tmp.sheaf.xif.paper.S172QPilotMultiradialImageActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
/-! # S317: qPilot and Theta COEFFICIENT SURROGATE on the same block
This is NOT the actual completion root Theta image.  The second object is the
scaled-region coefficient surrogate built from rootThetaImageSet and the
coefficient order/(2l); it is explicitly named CoefficientSurrogate.  The actual
root Theta image requires CompletionRootDataFamily T and is constructed in the
S310/S320 files, not here. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S317QPilotThetaCoefficientSurrogateActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Actual qPilot image point in the completion block (qVFamily q). -/
noncomputable def qPilotCompletionImagePoint : qVFamTensorBlock T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ()))
    (fun _ => ((qVFamily T b).q : CommonPrimeCompletion
      (qVFamTensorPlaces T b () ())))
/-- Coefficient surrogate family at b: order(q)/(2l).  NOT a root theta value. -/
noncomputable def coefficientSurrogateCoefficient : qVFamTensorV → Real :=
  fun _ => qVFamPaperRootCoefficient T b
/-- Coefficient-surrogate scaled image set on qVFamTensorBlock (NOT actual root). -/
noncomputable def coefficientSurrogateImageSet : Set (qVFamTensorBlock T b) :=
  rootThetaImageSet (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (completionRootThetaCoefficient T b)
/-- Coefficient-surrogate scaled hull on qVFamTensorBlock (NOT actual root). -/
noncomputable def coefficientSurrogateHull : Set (qVFamTensorBlock T b) :=
  rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (completionRootThetaCoefficient T b)
/-- Same-block coefficient-surrogate pair: qPilot point and scaled-region
coefficient image both on qVFamTensorBlock T b.  This does NOT assert the actual
completion root Theta image. -/
structure QPilotThetaCoefficientSurrogatePair where
  qPilot : qVFamTensorBlock T b
  qPilot_eq : qPilot = qPilotCompletionImagePoint T b
  thetaImage : Set (qVFamTensorBlock T b)
  thetaImage_eq : thetaImage = completionRootThetaImageSet T b
  thetaHull : Set (qVFamTensorBlock T b)
  thetaHull_eq : thetaHull = completionRootThetaHull T b
/-- Actual same-carrier pair. -/
noncomputable def qPilotThetaCoefficientSurrogatePair : QPilotThetaCompletionPair T b where
  qPilot := qPilotCompletionImagePoint T b
  qPilot_eq := rfl
  thetaImage := completionRootThetaImageSet T b
  thetaImage_eq := rfl
  thetaHull := completionRootThetaHull T b
  thetaHull_eq := rfl
end LeanFormal.IUT.XiFPaper.S317QPilotThetaSameCompletionBlockActual
