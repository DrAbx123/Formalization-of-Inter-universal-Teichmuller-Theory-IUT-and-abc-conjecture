import tmp.sheaf.xif.paper.S861RootCharacterNormComparisonActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
/-! # S865: general rootHaarFactor norm-power formula
Combines the actual DVR decomposition, multiplicativity, zpow law, unit
triviality and uniformizer formula. -/
noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S865RootHaarFactorNormPowActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionUnitDecompositionActual
open LeanFormal.IUT.XiFPaper.S284RootUniformizerFactorActual
open LeanFormal.IUT.XiFPaper.S295GeneralHaarFactorActual
open LeanFormal.IUT.XiFPaper.S300GeneralFactorNormActual
open LeanFormal.IUT.XiFPaper.S861RootCharacterNormComparisonActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
noncomputable def rootHaarFactorNormPowExactGoal : Prop :=
  RootHaarFactorNormPow (l := l) T b
    (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))
theorem rootHaarFactor_normPow_actual :
    RootHaarFactorNormPow (l := l) T b
      (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  intro lam
  obtain ⟨n, u, hlam⟩ := exists_unit_uniformizer_zpow (T := T) (b := b) lam
  let uL : (rootNormedExtension T b)ˣ :=
    Units.map (algebraMap (Integers (rootNormedExtension T b))
      (rootNormedExtension T b)).toMonoidHom u
  let d := Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
  let w : Real := ‖(rootUniformizerField T b : rootNormedExtension T b)‖
  have hu_norm : ‖(uL : rootNormedExtension T b)‖ = 1 := by
    change ‖((u : Integers (rootNormedExtension T b)) : rootNormedExtension T b)‖ = 1
    exact norm_unit_eq_one (K := rootNormedExtension T b) u
  have hfac : rootHaarFactor T b lam =
      (ENNReal.ofReal (w ^ d)) ^ n := by
    rw [hlam, rootHaarFactor_mul, rootHaarFactor_eq_one_of_norm_one (T := T) (b := b) uL hu_norm,
      one_mul, rootHaarFactor_zpow]
    rw [rootHaarFactor_uniformizer_eq_norm_pow (T := T) (b := b)]
  have hnorm : ‖(lam : rootNormedExtension T b)‖ = w ^ n := by
    rw [hlam]
    simp only [Units.val_mul]
    rw [norm_mul, hu_norm, one_mul]
    rw [Units.val_zpow_eq_zpow_val]
    rw [norm_zpow]
  rw [hfac, hnorm]
  have hwpos : 0 < w := by
    unfold w
    exact norm_pos_iff.mpr (Units.ne_zero (rootUniformizerField T b))
  have hne : Real.toNNReal (w ^ d) ≠ 0 := by
    intro hzero
    have hreal : (Real.toNNReal (w ^ d) : Real) = 0 := by exact_mod_cast hzero
    rw [Real.coe_toNNReal _ (by positivity)] at hreal
    exact (pow_ne_zero d hwpos.ne') hreal
  rw [show ENNReal.ofReal (w ^ d) =
      ((Real.toNNReal (w ^ d) : NNReal) : ENNReal) by rfl]
  rw [← ENNReal.coe_zpow hne]
  rw [show ENNReal.ofReal ((w ^ n) ^ d) =
      ((Real.toNNReal ((w ^ n) ^ d) : NNReal) : ENNReal) by rfl]
  congr 1
  apply NNReal.coe_injective
  rw [NNReal.coe_zpow, Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (by positivity)]
  have hd : (w ^ d : Real) = w ^ (d : Int) := by rw [zpow_natCast]
  have hd2 : (w ^ n) ^ d = (w ^ n) ^ (d : Int) := by rw [zpow_natCast]
  rw [hd, hd2, ← zpow_mul, ← zpow_mul]
  congr 1
  push_cast
  ring
theorem rootNormedCharacterNormComparison_actual :
    RootNormedCharacterNormComparison (l := l) T b
      (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) :=
  rootNormedCharacterNormComparison_of_factorNormPow (l := l) T b _
    (rootHaarFactor_normPow_actual (l := l) T b)
end LeanFormal.IUT.XiFPaper.S865RootHaarFactorNormPowActual
