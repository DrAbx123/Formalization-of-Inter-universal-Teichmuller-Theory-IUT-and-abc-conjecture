import tmp.sheaf.xif.paper.S730QVFamBlockLatticeAlignmentActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralLattice
/-! # S741: actual Zp-smul compatibility for qVFamBlockLinearEquiv
The Zp module on the tensor block and on rootBase is the scoped compHom module
through Qp.  Hence z • x = (z:Qp) • x definitionally, and Qp-linearity plus
map_smul gives the Zp compatibility. -/
noncomputable section
open scoped BigOperators LeanFormal.IUT.FinitePadicIntegralLattice
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S741QVFamBlockSMulActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S730QVFamBlockLatticeAlignmentActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.LocalFieldPadicTensor
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Actual Zp-smul compatibility. -/
theorem qVFamBlockSMulCompatibility_actual :
    QVFamBlockSMulCompatibility (l := l) T b := by
  intro z x
  rw [LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq,
    LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq,
    map_smul]
end LeanFormal.IUT.XiFPaper.S741QVFamBlockSMulActual
