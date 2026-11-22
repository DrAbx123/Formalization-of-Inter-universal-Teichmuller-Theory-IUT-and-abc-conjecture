import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S824RootStackyHaarVolumeActual
import tmp.sheaf.xif.paper.S312QPilotRootTensorBaseChangeActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual embedding of the qVFam block into the finite root-stack extension
L(mu_2l): qVFamBlock ≃ rootBase -> L -> L(mu). -/
noncomputable def rootStackEmbedding : qVFamTensorBlock T b → rootStackExtension T b :=
  fun x => algebraMap (rootNormedExtension T b) (rootStackExtension T b)
    (algebraMap (rootBase T b) (rootNormedExtension T b)
      (qVFamBlockLinearEquiv T b x))

/-- Paper theta hull on the root stack: image of the cRoot = order/(2l)
lambda-O region under the actual embedding. -/
noncomputable def rootStackPaperThetaHull : Set (rootStackExtension T b) :=
  rootStackEmbedding (l := l) T b ''
    paperLambdaORegion (l := l) T b (paperRootCoefficientFamily (l := l) T b)

/-- Actual inherited additive Haar from S782 on the root stack. -/
noncomputable def rootStackPaperThetaHaar : Measure (rootStackExtension T b) :=
  rootStackHaar (l := l) T b

/-- Normalized log of the transported paper theta hull, using the actual
root-stack Haar. -/
noncomputable def rootStackPaperThetaHullLog : Real :=
  Real.log ((rootStackPaperThetaHaar (l := l) T b
    (rootStackPaperThetaHull (l := l) T b)).toReal)

/-- Exact positivity/finiteness data for the root-stack hull log. -/
structure RootStackPaperThetaHullLogData where
  hull_pos : 0 < rootStackPaperThetaHaar (l := l) T b
    (rootStackPaperThetaHull (l := l) T b)
  hull_lt_top : rootStackPaperThetaHaar (l := l) T b
    (rootStackPaperThetaHull (l := l) T b) < ⊤
  log_eq : rootStackPaperThetaHullLog (l := l) T b =
    Real.log ((rootStackPaperThetaHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b)).toReal)

def RootStackPaperThetaHullLogRequired : Prop :=
  Nonempty (RootStackPaperThetaHullLogData (l := l) T b)

/-- Exact bridge: the transported lambda-O hull is the paper root theta hull
image in the finite root-stack extension. -/
def RootStackPaperThetaHullBridge : Prop :=
  rootStackPaperThetaHull (l := l) T b =
    rootStackEmbedding (l := l) T b ''
      paperRootThetaHull (l := l) T b

/-- Exact minimal data: hull bridge plus positivity/finiteness of the actual
root-stack Haar on the hull. -/
def S1073ExactMinimal : Prop :=
  RootStackPaperThetaHullBridge (l := l) T b ∧
    RootStackPaperThetaHullLogRequired (l := l) T b

end LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual

end
