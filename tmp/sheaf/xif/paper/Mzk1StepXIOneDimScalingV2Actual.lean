/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeDecompositionActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual

/-! # A564 one-dimensional p-scaling strict ball measure (minimal, clean file) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIOneDimScalingV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

noncomputable def primeFactor : ℝ :=
  (‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (qVFamTensorP T b) : rootNormedExtension T b)‖) ^
    Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)

theorem primeFactor_pos : 0 < primeFactor T b := by
  unfold primeFactor
  rw [rootNorm_algebraMap_prime (T := T) (b := b), Padic.norm_p]
  apply pow_pos
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)

theorem primeFactor_lt_one : primeFactor T b < 1 := by
  unfold primeFactor
  rw [rootNorm_algebraMap_prime (T := T) (b := b), Padic.norm_p]
  have hp : (1 : ℝ) < (qVFamTensorP T b : ℝ) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  have hinv : (qVFamTensorP T b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hnonneg : (0 : ℝ) ≤ (qVFamTensorP T b : ℝ)⁻¹ := by positivity
  have hd : Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) ≠ 0 :=
    Nat.ne_of_gt Module.finrank_pos
  exact pow_lt_one₀ hnonneg hinv hd

theorem prime_smul_closedBall (R : ℝ) (hR : 0 ≤ R) :
    (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
        Metric.closedBall (0 : rootNormedExtension T b) R =
      Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : ℝ)) := by
  let L := rootNormedExtension T b
  have hp_pos : (0 : ℝ) < (qVFamTensorP T b : ℝ) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
  have hp_ne : (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hy ⊢
    change ‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) (qVFamTensorP T b)) * y‖ ≤ R / (qVFamTensorP T b : Real)
    rw [norm_mul, rootNorm_algebraMap_prime, Padic.norm_p]
    calc (qVFamTensorP T b : ℝ)⁻¹ * ‖y‖ ≤ (qVFamTensorP T b : ℝ)⁻¹ * R := by
          gcongr
      _ = R / (qVFamTensorP T b : ℝ) := by rw [div_eq_inv_mul]
  · intro hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    refine ⟨(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
        (qVFamTensorP T b))⁻¹ * x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_inv,
        rootNorm_algebraMap_prime, Padic.norm_p]
      have hnorm : ((qVFamTensorP T b : ℝ)⁻¹)⁻¹ = (qVFamTensorP T b : ℝ) := by
        field_simp
      rw [hnorm]
      calc (qVFamTensorP T b : ℝ) * ‖x‖ ≤
            (qVFamTensorP T b : ℝ) * (R / (qVFamTensorP T b : ℝ)) := by
            gcongr
        _ = R := by field_simp
    · change (algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) (qVFamTensorP T b)) * ((algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) (qVFamTensorP T b))⁻¹ * x) = x
      field_simp

theorem rootExtensionHaar_ball_strict (R : ℝ) (hR : 0 < R) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : ℝ))) <
      rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) := by
  have hsm := rootPrime_smul_measure (T := T) (b := b)
    (Metric.closedBall (0 : rootNormedExtension T b) R)
  rw [prime_smul_closedBall T b R hR.le] at hsm
  have hfinF : rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) < ⊤ :=
    rootExtensionClosedBall_measure_lt_top (T := T) (b := b) R
  have hfinH : rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (R / (qVFamTensorP T b : ℝ))) < ⊤ :=
    rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _
  have hposF : 0 < rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) :=
    rootExtensionClosedBall_measure_pos (T := T) (b := b) R hR
  have hto : (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (R / (qVFamTensorP T b : ℝ)))).toReal =
      primeFactor T b * (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal := by
    rw [hsm, ENNReal.toReal_mul]
    congr 1
    unfold primeFactor
    rw [ENNReal.toReal_ofReal (by positivity)]
  refine (ENNReal.toReal_lt_toReal (ne_of_lt hfinH) (ne_of_lt hfinF)).mp ?_
  have hposFreal : 0 < (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hposF) (ne_of_lt hfinF)
  rw [hto]
  calc primeFactor T b * (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal
      < 1 * (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal :=
        mul_lt_mul_of_pos_right (primeFactor_lt_one T b) hposFreal
    _ = (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal := one_mul _

end LeanFormal.IUT.XiFPaper.Mzk1StepXIOneDimScalingV2Actual

end