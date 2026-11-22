import tmp.sheaf.xif.paper.S879RootStackNormFormulaInputsActual
/-! # S886: E/L norm-extension formula is actual
rootStackExtension is an IntermediateField of rootNormedAmbient, and both
norms are the inherited ambient spectral norm. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S886ENormExtensionFormulaActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S879RootStackNormFormulaInputsActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
theorem eNormExtensionFormula_actual :
    ENormExtensionFormula (l := l) T b := by
  intro x
  change ‖(x : rootNormedAmbient T b)‖ = ‖(x : rootNormedAmbient T b)‖
  rfl
theorem rootStackNormFormulaInputs_actual :
    ENormExtensionFormula (l := l) T b := eNormExtensionFormula_actual (l := l) T b
end LeanFormal.IUT.XiFPaper.S886ENormExtensionFormulaActual
