/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.Mzk1S1915DegreeFinrankActual
import Mathlib.Tactic

/-! # P2 (R1.3): exact relative root mass difference and its nonnegativity -/

/-
| field | value |
|---|---|
| Status | PROVED: `p2RExact = Σ_b d_b(log‖λ_b‖−log‖qhat_b‖) = −Σ_b d_b log‖c_b‖ ≥ 0` (from `qhat=λ·c`, `c∈O`); exact difference to `c0RemainderV2` recorded |
| GAP | `c0RemainderV2` is NOT equal to `p2RExact` in general; their difference is an explicit sum (`p2RExact = c0RemainderV2 + correction`), no equality assumed |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2RelativeMassActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1S1915DegreeFinrankActual
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Nonvanishing of `lambda_b` and `qhat_b` at each bad place. -/
theorem p2_lambda_ne_zero (b : Bad (nativePlaceSelection T)) :
    rootThetaFieldLambda T b ≠ 0 := by
  have hpos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← rootImageRadius_eq_norm_fieldLambda]
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  exact norm_ne_zero_iff.mp (ne_of_gt hpos)

theorem p2_qhat_ne_zero (b : Bad (nativePlaceSelection T)) :
    c0QHat T b ≠ 0 := by
  unfold c0QHat c0Alpha
  exact pow_ne_zero _ (qrootElem_ne_zero T b)

theorem p2Coeff_ne_zero (b : Bad (nativePlaceSelection T)) :
    p2Coefficient T b ≠ 0 :=
  div_ne_zero (p2_qhat_ne_zero T b) (p2_lambda_ne_zero T b)

/-- (R1.3) step 1: `log‖qhat‖ = log‖λ‖ + log‖c‖`. -/
theorem p2_log_norm_qhat_eq_add (b : Bad (nativePlaceSelection T)) :
    Real.log ‖c0QHat T b‖ =
      Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ +
        Real.log ‖p2Coefficient T b‖ := by
  rw [p2QHat_eq_lambda_mul_coefficient T b, norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.mpr (p2_lambda_ne_zero T b))
    (norm_ne_zero_iff.mpr (p2Coeff_ne_zero T b))

/-- **R1.3 exact relative mass difference** `Σ_b d_b(log‖λ_b‖−log‖qhat_b‖)`. -/
noncomputable def p2RExact : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
      (Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ -
        Real.log ‖c0QHat T b‖)

/-- Same expression with `s1915LocalDegree` (definitionally equal to `finrank`). -/
theorem p2RExact_eq_s1915_degrees :
    p2RExact T =
      ∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) *
          (Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ -
            Real.log ‖c0QHat T b‖) := by
  unfold p2RExact
  apply Finset.sum_congr rfl
  intro b _
  rw [s1915LocalDegree_eq_finrank T b]

/-- (R1.3) step 2: `R_exact = −Σ_b d_b log‖c_b‖`. -/
theorem p2RExact_eq_neg_sum_log_coeff :
    p2RExact T =
      -∑ b : Bad (nativePlaceSelection T),
        (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
          Real.log ‖p2Coefficient T b‖ := by
  unfold p2RExact
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [p2_log_norm_qhat_eq_add T b]
  ring

/-- (R1.3) step 3: `R_exact >= 0` (finite sum of nonnegative terms). -/
theorem p2RExact_nonneg : 0 ≤ p2RExact T := by
  rw [p2RExact_eq_neg_sum_log_coeff T, ← Finset.sum_neg_distrib]
  apply Finset.sum_nonneg
  intro b _
  have hcpos : 0 < ‖p2Coefficient T b‖ :=
    norm_pos_iff.mpr (p2Coeff_ne_zero T b)
  have hle : ‖p2Coefficient T b‖ ≤ 1 := p2Coefficient_norm_le_one T b
  have hlog : Real.log ‖p2Coefficient T b‖ ≤ 0 :=
    Real.log_nonpos (le_of_lt hcpos) hle
  have hd : 0 ≤ (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) :=
    Nat.cast_nonneg _
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hd hlog)

/-- Exact correction comparing `R_exact` with `c0RemainderV2`:
`R_exact = c0RemainderV2 + Σ_b d_b((2l−1)log‖λ_b‖ − log‖c_b‖)`. -/
noncomputable def p2RExactCorrection : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
      (((2 * (l.value : Real) - 1) *
          Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖) -
        Real.log ‖p2Coefficient T b‖)

/-- **(R1.3) exact difference**: `R_exact = c0RemainderV2 + p2RExactCorrection`;
no equality between the two is assumed. -/
theorem p2RExact_eq_c0RemainderV2_add_correction :
    p2RExact T = c0RemainderV2 T + p2RExactCorrection T := by
  unfold p2RExact c0RemainderV2 p2RExactCorrection
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [p2_log_norm_qhat_eq_add T b]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1P2RelativeMassActual