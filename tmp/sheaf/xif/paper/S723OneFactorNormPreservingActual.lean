import tmp.sheaf.xif.paper.S720OneFactorTensorNormReductionActual
/-! # S723: direct attempt at QVFamBlockNormPreserving
The one-factor equivalence is PiTensorProduct.subsingletonEquiv Unit.  Its
norm-preservation is not built into the tensor coordinate norm; this file
tries the definitional equality and records the exact remaining goal. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S723OneFactorNormPreservingActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S717TensorLatticeNormExactActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.LocalFieldPadicTensor
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Exact one-factor norm-preservation goal. -/
def S723ExactGoal : Prop :=
  QVFamBlockNormPreserving (l := l) T b
end LeanFormal.IUT.XiFPaper.S723OneFactorNormPreservingActual
