import LeanFormal.IUT.Foundations.PAdicAnalytic.TateJGeneral
import LeanFormal.IUT.Foundations.PAdicAnalytic.GeneralPSEval
import LeanFormal.IUT.Foundations.PAdicAnalytic.TatePSEvalIdentity
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesGeneral

open scoped ArithmeticFunction.sigma
open ArithmeticFunction PowerSeries
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.PAdicAnalytic.General

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

theorem eval_invOfUnit_C4K_cube (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1) q =
      (generalPSEval (C4K (K := K) ^ 3) q)⁻¹ := by
  have hf : PowerSeriesIntegral (C4K (K := K) ^ 3) :=
    integral_pow (integral_C4K (K := K) hint) 3
  have hconst : PowerSeries.constantCoeff (C4K (K := K) ^ 3) = 1 := by
    rw [map_pow]
    have hc4 : PowerSeries.constantCoeff (C4K (K := K)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact coeff_C4K_zero (K := K)
    rw [hc4]; norm_num
  have hfi : PowerSeriesIntegral (PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1) :=
    integral_invOfUnit (K := K) hint hf hconst
  have hmul := congrArg (fun s => generalPSEval s q)
    (PowerSeries.mul_invOfUnit (C4K (K := K) ^ 3) 1 hconst)
  rw [generalPSEval_mul _ _ hf hfi hq, generalPSEval_one] at hmul
  exact (inv_eq_of_mul_eq_one_right hmul).symm

theorem generalPSEval_HK_eq (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (h1728 : ‖(1728 : K)‖ = 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (HK (K := K)) q =
      generalPSEval (DK (K := K)) q /
        (generalPSEval (C4K (K := K)) q) ^ 3 := by
  have hD : PowerSeriesIntegral (DK (K := K)) :=
    integral_DK (K := K) hint h1728
  have h4 : PowerSeriesIntegral (C4K (K := K) ^ 3) :=
    integral_pow (integral_C4K (K := K) hint) 3
  have hconst : PowerSeries.constantCoeff (C4K (K := K) ^ 3) = 1 := by
    rw [map_pow]
    have hc4 : PowerSeries.constantCoeff (C4K (K := K)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact coeff_C4K_zero (K := K)
    rw [hc4]; norm_num
  have hInv : PowerSeriesIntegral (PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1) :=
    integral_invOfUnit (K := K) hint h4 hconst
  rw [HK, generalPSEval_mul _ _ hD hInv hq,
    eval_invOfUnit_C4K_cube (K := K) hint hq,
    eval_C4K_pow_three (K := K) hint hq,
    div_eq_mul_inv]

theorem generalPSEval_HK_eq_tateHK (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (h1728 : ‖(1728 : K)‖ = 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (HK (K := K)) q = tateHK (K := K) q := by
  rw [generalPSEval_HK_eq hint h1728 hq,
    generalPSEval_DK_eq_delta_closed hint h1728 hq,
    generalPSEval_C4K_eq_c4_closed hint hq]
  rfl

theorem tateHK_eq_q_add_generalTateR (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (h1728 : ‖(1728 : K)‖ = 1) {q : K} (hq : ‖q‖ < 1) :
    tateHK (K := K) q = q + generalTateR (K := K) q := by
  rw [← generalPSEval_HK_eq_tateHK hint h1728 hq]
  exact eval_HK_eq_q_add_generalTateR_of_hint hint h1728 hq

end LeanFormal.IUT.PAdicAnalytic.General
