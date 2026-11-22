import tmp.sheaf.xif.paper.S671QPilotRadiusAuditActual
/-! # S687: second half of the S678 reduction
The source-region estimate C * ‖x‖ ≤ rootImageRadius is reduced to the actual
fractional-lattice region radius R (norm bound on qPilotClassicalRegion) and
the scalar inequality C * R ≤ rootImageRadius.  With C = 1 this is exactly
the region norm bound by rootImageRadius.  No operator or source estimate is
fabricated. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S687QPilotSourceNormBoundActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)
/-- Concrete region radius: the fractional-lattice scaled qPilot region is
contained in the norm ball of radius R. -/
def QPilotRegionNormLe (R : Real) : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm →
      ‖x‖ ≤ R
/-- The S678 source-region norm bound, restated here to avoid importing the
currently non-compiling S678 file. -/
def QPilotSourceNormBound (C : Real) : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm →
      C * ‖x‖ ≤ (rootImageRadius T b : Real)
/-- Second half of the S678 reduction from an actual region radius. -/
theorem qPilotSourceNormBound_of_regionRadius
    (C R : Real) (hC : 0 ≤ C)
    (hregion : QPilotRegionNormLe (l := l) T b cNorm R)
    (hCR : C * R ≤ (rootImageRadius T b : Real)) :
    QPilotSourceNormBound (l := l) T b cNorm C := by
  intro x hx
  calc
    C * ‖x‖ ≤ C * R := mul_le_mul_of_nonneg_left (hregion x hx) hC
    _ ≤ (rootImageRadius T b : Real) := hCR
/-- C = 1 specialization: the exact region norm bound by rootImageRadius. -/
theorem qPilotSourceNormBound_one_of_regionRadius
    (hregion : QPilotRegionNormLe (l := l) T b cNorm
      (rootImageRadius T b : Real)) :
    QPilotSourceNormBound (l := l) T b cNorm 1 := by
  exact qPilotSourceNormBound_of_regionRadius (l := l) T b cNorm 1
    (rootImageRadius T b : Real) zero_le_one hregion (by simp)
/-- Exact minimal source inequality for the second half. -/
def QPilotSourceNormBoundExactGoal : Prop :=
  ∃ C : Real, 0 < C ∧ QPilotSourceNormBound (l := l) T b cNorm C
/-- Exact minimal region inequality, the concrete form of the goal. -/
def QPilotRegionNormExactGoal : Prop :=
  QPilotRegionNormLe (l := l) T b cNorm (rootImageRadius T b : Real)
end LeanFormal.IUT.XiFPaper.S687QPilotSourceNormBoundActual
