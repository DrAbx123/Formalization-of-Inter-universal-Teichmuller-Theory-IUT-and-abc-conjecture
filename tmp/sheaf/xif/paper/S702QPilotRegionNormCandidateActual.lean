import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S702QPilotRegionNormCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Candidate q-pilot region radius p^(-N), N = qVFamily order. -/
noncomputable def qPilotRegionRadiusCandidate : Real :=
  Real.rpow (qVFamTensorP T b : Real)
    (-((qVFamily T b).order : Real))

/-- Candidate root image radius p^(-N/(2l)). -/
noncomputable def qPilotRootImageRadiusCandidate : Real :=
  Real.rpow (qVFamTensorP T b : Real)
    (-((qVFamily T b).order : Real) / (2 * (l.value : Real)))

/-- The arithmetic candidate inequality. -/
def QPilotRegionNormCandidate : Prop :=
  qPilotRegionRadiusCandidate T b ≤ qPilotRootImageRadiusCandidate T b

/-- Actual arithmetic candidate inequality. -/
theorem qPilotRegionNormCandidate_actual : QPilotRegionNormCandidate T b := by
  unfold QPilotRegionNormCandidate qPilotRegionRadiusCandidate
    qPilotRootImageRadiusCandidate
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt.le
  · have hN : (0 : Real) ≤ ((qVFamily T b).order : Real) := by positivity
    have hl : (1 : Real) ≤ (2 * (l.value : Real)) := by
      have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
      nlinarith
    have hden : (0 : Real) < 2 * (l.value : Real) := by linarith
    have hle : ((qVFamily T b).order : Real) / (2 * (l.value : Real)) ≤
        ((qVFamily T b).order : Real) := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hneg : (-((qVFamily T b).order : Real)) / (2 * (l.value : Real)) =
        -(((qVFamily T b).order : Real) / (2 * (l.value : Real))) := by ring
    rw [hneg]
    linarith

end LeanFormal.IUT.XiFPaper.S702QPilotRegionNormCandidateActual

end
