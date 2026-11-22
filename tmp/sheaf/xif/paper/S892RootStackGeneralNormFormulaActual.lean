import tmp.sheaf.xif.paper.S887RootStackHaarDetViaS861EActual
import tmp.sheaf.xif.paper.S886ENormExtensionFormulaActual
import tmp.sheaf.xif.paper.S865RootHaarFactorNormPowActual
/-! # S892: general norm formula from L-layer, norm extension, and E comparison
Uses S865 (actual L character), S886 (actual norm extension), S887 reduction and
the exact E character/determinant-Haar input. -/
noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S892RootStackGeneralNormFormulaActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S866RootStackCharacterNormLiftActual
open LeanFormal.IUT.XiFPaper.S870RootStackRestrictionBridgeActual
open LeanFormal.IUT.XiFPaper.S879RootStackNormFormulaInputsActual
open LeanFormal.IUT.XiFPaper.S887RootStackHaarDetViaS861EActual
open LeanFormal.IUT.XiFPaper.S886ENormExtensionFormulaActual
open LeanFormal.IUT.XiFPaper.S865RootHaarFactorNormPowActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Actual norm-extension formula for units. -/
theorem rootStackNormExtensionFormula_actual :
    RootStackNormExtensionFormula (l := l) T b := by
  intro u
  simpa [rootStackAlgebraMapUnits] using
    eNormExtensionFormula_actual (l := l) T b (x := (u : rootNormedExtension T b))
/-- L dimension equals dK*dLK. -/
theorem finrankL_eq_dK_mul_dLK :
    Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) =
      dK (l := l) T b * dLK (l := l) T b := by
  rw [dK, dLK]
  exact (Module.finrank_mul_finrank ℚ_[(qVFamTensorP T b)]
    (rootBase T b) (rootNormedExtension T b)).symm
/-- General norm formula from the exact E character input. -/
theorem rootStackGeneralNormFormula_of_ECharacter
    (hE : RootStackCharacterNormComparisonAtDQp (l := l) T b) :
    RootStackGeneralNormFormula (l := l) T b :=
  rootStackGeneralNormFormula_of_S861E_S861L_norm (l := l) T b
    (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))
    (finrankL_eq_dK_mul_dLK (l := l) T b) hE
    (rootNormedCharacterNormComparison_actual (l := l) T b)
    (rootStackNormExtensionFormula_actual (l := l) T b)
/-- Exact E analytic input still missing: determinant/additive-Haar character
comparison at dQpFactor. -/
def RootStackGeneralNormFormulaExactGoal : Prop :=
  RootStackCharacterNormComparisonAtDQp (l := l) T b
end LeanFormal.IUT.XiFPaper.S892RootStackGeneralNormFormulaActual
