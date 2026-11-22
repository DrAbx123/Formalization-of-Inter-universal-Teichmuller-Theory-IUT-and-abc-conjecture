import tmp.sheaf.xif.paper.S300GeneralFactorNormActual
import tmp.sheaf.xif.paper.S284RootUniformizerFactorActual
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
/-! # S861: rootNormedExtension character/norm comparison
Reduces the character/norm comparison to the exact general rootHaarFactor
norm-power formula.  The DVR decomposition, multiplicativity, unit triviality
and uniformizer formula are actual; the general lambda formula is exact. -/
noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S861RootCharacterNormComparisonActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.S284RootUniformizerFactorActual
open LeanFormal.IUT.XiFPaper.S295GeneralHaarFactorActual
open LeanFormal.IUT.XiFPaper.S300GeneralFactorNormActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Root character/norm comparison at exponent n. -/
def RootNormedCharacterNormComparison (n : Nat) : Prop :=
  ∀ lam : (rootNormedExtension T b)ˣ,
    Real.log (distribHaarChar (rootNormedExtension T b) lam : Real) =
      (n : Real) * Real.log ‖(lam : rootNormedExtension T b)‖
/-- Exact general rootHaarFactor norm-power formula. -/
def RootHaarFactorNormPow (n : Nat) : Prop :=
  ∀ lam : (rootNormedExtension T b)ˣ,
    rootHaarFactor T b lam = ENNReal.ofReal
      ((‖(lam : rootNormedExtension T b)‖) ^ n)
/-- The comparison follows from the general factor formula. -/
theorem rootNormedCharacterNormComparison_of_factorNormPow
    (n : Nat) (h : RootHaarFactorNormPow (l := l) T b n) :
    RootNormedCharacterNormComparison (l := l) T b n := by
  intro lam
  have hfac := h lam
  have hto : (rootHaarFactor T b lam).toReal =
      (‖(lam : rootNormedExtension T b)‖) ^ n := by
    rw [hfac, ENNReal.toReal_ofReal (by positivity)]
  have hlog : Real.log (distribHaarChar (rootNormedExtension T b) lam : Real) =
      Real.log ((rootHaarFactor T b lam).toReal) := by
    unfold rootHaarFactor
    rw [ENNReal.coe_toReal]
  rw [hlog, hto, Real.log_pow]
/-- Exact remaining general factor goal. -/
def RootHaarFactorNormPowExactGoal : Prop :=
  RootHaarFactorNormPow (l := l) T b
    (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))
end LeanFormal.IUT.XiFPaper.S861RootCharacterNormComparisonActual
