import tmp.sheaf.xif.paper.S730QVFamBlockLatticeAlignmentActual
import tmp.sheaf.xif.paper.S734PaperCoefficientBridgeActual
import tmp.sheaf.xif.paper.S664RootQUnitNormLeOneActual
import tmp.sheaf.xif.paper.S723OneFactorNormPreservingActual
import tmp.sheaf.xif.paper.S717TensorLatticeNormExactActual
import tmp.sheaf.xif.paper.S727RootThetaOneNormFormulaActual
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Probe2
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

macro "port" : tactic => `(tactic|
  first
  | linarith
  | nlinarith
  | positivity
  | norm_num
  | gcongr
  | (field_simp; ring)
  | omega
  | simp
  | grind
  | aesop
  | fail "NOT_CLOSED")

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

-- @ B1 QVFamBlockNormPreserving, portfolio
example : LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual.QVFamBlockNormPreserving (l := l) T b := by port

-- @ B1s QVFamBlockNormPreserving, intro+simp
example : LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual.QVFamBlockNormPreserving (l := l) T b := by
  intro x
  simp only [LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual.qVFamBlockLinearEquiv]

-- @ B1r QVFamBlockNormPreserving, intro+rfl
example : LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual.QVFamBlockNormPreserving (l := l) T b := by
  intro x
  rfl

-- @ B5a RootQUnitNormLeOne, portfolio
example : LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual.RootQUnitNormLeOne (T := T) := by port

-- @ B5b RootQUnitNormLeOne, intro b; exact?
example : LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual.RootQUnitNormLeOne (T := T) := by
  intro b
  exact (qNorm_lt_one (qVFamily T b)).le

-- @ B9 RootThetaOneNormFormula, portfolio
example : LeanFormal.IUT.XiFPaper.S718RootImageRadiusLowerActual.RootThetaOneNormFormula (l := l) T b := by port

-- @ B7 ctrl QVFamBlockSMulCompatibility, explicit rw
example : LeanFormal.IUT.XiFPaper.S730QVFamBlockLatticeAlignmentActual.QVFamBlockSMulCompatibility (l := l) T b := by
  intro z x
  exact map_smul _ z x

-- @ B8 ctrl paper root coefficient, exact theorem
example : LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual.qVFamPaperRootCoefficient T b ≤
    LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b :=
  LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual.qVFamPaperRootCoefficient_le_normalized T b

end Probe2
