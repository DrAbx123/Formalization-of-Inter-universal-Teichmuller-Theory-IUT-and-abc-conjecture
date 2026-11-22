import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual norm bound for the source qVFamily unit. -/
theorem rootQUnitNormLeOne : RootQUnitNormLeOne (T := T) := by
  intro b
  have h := (qNorm_lt_one (qVFamily T b)).le
  have hiff := normalizedCompletion_norm_le_one_iff (qVFamTensorPlace T b)
    ((qVFamily T b).q : NormalizedCompletion (qVFamTensorPlace T b))
  have hleft : ‖normalizedCompletionRingEquiv (qVFamTensorPlace T b)
      ((qVFamily T b).q : NormalizedCompletion (qVFamTensorPlace T b))‖ ≤ 1 := by
    rw [normalizedCompletionRingEquiv]
    exact h
  letI := normalizedCompletionNontriviallyNormedField (qVFamTensorPlace T b)
  have hnorm := hiff.mp hleft
  simpa [sourceRootQUnit, Units.val_mk0] using hnorm

end LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual

end
