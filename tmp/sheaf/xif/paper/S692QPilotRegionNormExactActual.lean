import tmp.sheaf.xif.paper.S687QPilotSourceNormBoundActual
/-! # S692: exact reduction of QPilotRegionNormExactGoal
The qPilot classical region is thetaTensorScaledRegion at cNorm; the actual
coefficient comparison gives its inclusion in the root-label region at j=1,
whose coefficient is c_root <= c_norm.  The remaining concrete inequality is
the root-label-region norm bound by rootImageRadius. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S692QPilotRegionNormExactActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual
open LeanFormal.IUT.XiFPaper.S687QPilotSourceNormBoundActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)
/-- Norm bound for a general theta tensor scaled region. -/
def ThetaScaledRegionNormLe (c : qVFamTensorV → Real) (R : Real) : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple) c → ‖x‖ ≤ R
/-- The qPilot region is exactly the scaled region at cNorm. -/
theorem qPilotRegionNormLe_iff_scaled :
    QPilotRegionNormLe (l := l) T b cNorm (rootImageRadius T b : Real) ↔
      ThetaScaledRegionNormLe (l := l) T b cNorm
        (rootImageRadius T b : Real) := by
  unfold QPilotRegionNormLe ThetaScaledRegionNormLe
    qPilotClassicalRegion
  rfl
def S692ExactGoal : Prop :=
  QPilotRegionNormExactGoal (l := l) T b cNorm
end LeanFormal.IUT.XiFPaper.S692QPilotRegionNormExactActual
