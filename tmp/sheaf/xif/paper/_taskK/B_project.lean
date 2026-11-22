import tmp.sheaf.xif.paper.S730QVFamBlockLatticeAlignmentActual
import tmp.sheaf.xif.paper.S734PaperCoefficientBridgeActual
import tmp.sheaf.xif.paper.S664RootQUnitNormLeOneActual
import tmp.sheaf.xif.paper.S723OneFactorNormPreservingActual
import tmp.sheaf.xif.paper.S717TensorLatticeNormExactActual
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Probe
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S717TensorLatticeNormExactActual
open LeanFormal.IUT.XiFPaper.S708QPilotRootLabelRegionNormActual
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

-- @ B1 QVFamBlockNormPreserving (S720/S723)
example : QVFamBlockNormPreserving (l := l) T b := by port

-- @ B1r QVFamBlockNormPreserving by rfl
example : QVFamBlockNormPreserving (l := l) T b := by
  intro x
  rfl

-- @ B2 TensorFractionalLatticeNormLemma (S717)
example (c : qVFamTensorV → Real) : TensorFractionalLatticeNormLemma (l := l) T b c := by port

-- @ B3 QVFamBlockMapsFractionalLattice (S720)
example (c : qVFamTensorV → Real) : QVFamBlockMapsFractionalLattice (l := l) T b c := by port

-- @ B4 S708ExactGoal
example : S708ExactGoal (l := l) T b := by port

-- @ B5 RootQUnitNormLeOne (S664 target)
example : RootQUnitNormLeOne (T := T) := by port

-- @ B6 S717CorrectedRootLabelRegionNormBound
example : S717CorrectedRootLabelRegionNormBound (l := l) T b := by port

-- @ B7 QVFamBlockSMulCompatibility (S730, proved)
example : LeanFormal.IUT.XiFPaper.S730QVFamBlockLatticeAlignmentActual.QVFamBlockSMulCompatibility (l := l) T b := by port

-- @ B8 paper root coefficient inequality (proved)
example : LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual.qVFamPaperRootCoefficient T b ≤
    LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b := by port

-- @ B9 rootThetaOneNormFormula (S727, proved)
example : RootThetaOneNormFormula (l := l) T b := by port

end Probe
