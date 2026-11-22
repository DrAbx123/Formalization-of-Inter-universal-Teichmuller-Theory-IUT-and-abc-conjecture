import LeanFormal.IUT.Foundations.PAdicAnalytic.GeneralPSEval
import LeanFormal.IUT.Foundations.PAdicAnalytic.GeneralLambertAntidiagonal
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import Mathlib.Tactic

open scoped ArithmeticFunction.sigma
open ArithmeticFunction PowerSeries
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic.General

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

/-- Divisor-sum series over N, with zero constant coefficient. -/
noncomputable def sigmaSeriesQ (k : ℕ) (q : K) : K :=
  ∑' n : ℕ, (ArithmeticFunction.sigma k n : K) * q ^ n

lemma sigmaSeries_eq_sigmaSeriesQ (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    LeanFormal.IUT.PAdicAnalytic.sigmaSeries (K := K) k q = sigmaSeriesQ (K := K) k q := by
  let f : ℕ → K := fun n => (σ k n : K) * q ^ n
  have hf_summable : Summable f := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => ‖q‖ ^ n)
      (summable_geometric_of_lt_one (norm_nonneg q) hq) ?_
    intro n
    change ‖(σ k n : K) * q ^ n‖ ≤ ‖q‖ ^ n
    rw [norm_mul, norm_pow]
    have hσ : ‖(σ k n : K)‖ ≤ 1 := hint _
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg q) n) hσ
  have hf0 : f 0 = 0 := by
    simp [f, ArithmeticFunction.sigma_apply]
  rw [LeanFormal.IUT.PAdicAnalytic.sigmaSeries, sigmaSeriesQ,
    tsum_pnat_eq_tsum_succ (f := f)]
  rw [hf_summable.tsum_eq_zero_add, hf0, zero_add]

theorem lambertSeries_eq_sigmaSeriesQ_three (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K 3 q = sigmaSeriesQ (K := K) 3 q := by
  rw [LeanFormal.IUT.PAdicAnalytic.lambertSeries_eq_sigmaSeries_three hint hq]
  exact sigmaSeries_eq_sigmaSeriesQ hint 3 hq

theorem lambertSeries_eq_sigmaSeriesQ_five (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K 5 q = sigmaSeriesQ (K := K) 5 q := by
  rw [LeanFormal.IUT.PAdicAnalytic.lambertSeries_eq_sigmaSeries_five hint hq]
  exact sigmaSeries_eq_sigmaSeriesQ hint 5 hq

theorem generalPSEval_S3K_eq_sigmaSeriesQ (q : K) :
    generalPSEval (S3K (K := K)) q = sigmaSeriesQ (K := K) 3 q := by
  unfold generalPSEval sigmaSeriesQ S3K
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst hn; simp [sigmaCoeff]
  · simp [sigmaCoeff, hn]

theorem generalPSEval_S5K_eq_sigmaSeriesQ (q : K) :
    generalPSEval (S5K (K := K)) q = sigmaSeriesQ (K := K) 5 q := by
  unfold generalPSEval sigmaSeriesQ S5K
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst hn; simp [sigmaCoeff]
  · simp [sigmaCoeff, hn]

theorem generalPSEval_C4K_eq (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (C4K (K := K)) q =
      1 + 240 * sigmaSeriesQ (K := K) 3 q := by
  have h1 : PowerSeriesIntegral (1 : PowerSeries K) := integral_one
  have hC : PowerSeriesIntegral (PowerSeries.C (240 : K)) := integral_C (hint 240)
  have hS : PowerSeriesIntegral (S3K (K := K)) := integral_S3K (K := K) hint
  have hCS : PowerSeriesIntegral (PowerSeries.C (240 : K) * S3K (K := K)) :=
    integral_mul hC hS
  rw [C4K, generalPSEval_add _ _ h1 hCS hq, generalPSEval_one,
    generalPSEval_mul _ _ hC hS hq, generalPSEval_C,
    generalPSEval_S3K_eq_sigmaSeriesQ]

theorem generalPSEval_C6K_eq (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (C6K (K := K)) q =
      -1 + 504 * sigmaSeriesQ (K := K) 5 q := by
  have h1 : PowerSeriesIntegral (1 : PowerSeries K) := integral_one
  have hC : PowerSeriesIntegral (PowerSeries.C (504 : K)) := integral_C (hint 504)
  have hS : PowerSeriesIntegral (S5K (K := K)) := integral_S5K (K := K) hint
  have hCS : PowerSeriesIntegral (PowerSeries.C (504 : K) * S5K (K := K)) :=
    integral_mul hC hS
  rw [C6K, generalPSEval_add _ _ (integral_neg h1) hCS hq,
    generalPSEval_neg, generalPSEval_one,
    generalPSEval_mul _ _ hC hS hq, generalPSEval_C,
    generalPSEval_S5K_eq_sigmaSeriesQ]

theorem tateCurve_c4_eq_general (q : K) :
    (TateCurve.weierstrassCurve K q).c₄ =
      1 + 240 * TateCurve.lambertSeries K 3 q := by
  simp [TateCurve.weierstrassCurve, TateCurve.a4, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem tateCurve_c6_eq_general (q : K) :
    (TateCurve.weierstrassCurve K q).c₆ =
      -1 + 504 * TateCurve.lambertSeries K 5 q := by
  simp [TateCurve.weierstrassCurve, TateCurve.a4, TateCurve.a6,
    WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  field_simp
  ring

theorem generalPSEval_C4K_eq_c4_closed (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (C4K (K := K)) q = (TateCurve.weierstrassCurve K q).c₄ := by
  rw [generalPSEval_C4K_eq hint hq, tateCurve_c4_eq_general,
    lambertSeries_eq_sigmaSeriesQ_three hint hq]

theorem generalPSEval_C6K_eq_c6_closed (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (C6K (K := K)) q = (TateCurve.weierstrassCurve K q).c₆ := by
  rw [generalPSEval_C6K_eq hint hq, tateCurve_c6_eq_general,
    lambertSeries_eq_sigmaSeriesQ_five hint hq]

theorem eval_C4K_pow_three (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (C4K (K := K) ^ 3) q =
      (generalPSEval (C4K (K := K)) q) ^ 3 :=
  generalPSEval_pow (C4K (K := K)) 3 (integral_C4K (K := K) hint) hq

theorem eval_C6K_pow_two (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (C6K (K := K) ^ 2) q =
      (generalPSEval (C6K (K := K)) q) ^ 2 :=
  generalPSEval_pow (C6K (K := K)) 2 (integral_C6K (K := K) hint) hq

theorem eval_DK (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (h1728 : ‖(1728 : K)‖ = 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (DK (K := K)) q =
      (generalPSEval (C4K (K := K) ^ 3) q -
        generalPSEval (C6K (K := K) ^ 2) q) * ((1728 : K)⁻¹) := by
  have h4 : PowerSeriesIntegral (C4K (K := K) ^ 3) :=
    integral_pow (integral_C4K (K := K) hint) 3
  have h6 : PowerSeriesIntegral (C6K (K := K) ^ 2) :=
    integral_pow (integral_C6K (K := K) hint) 2
  have hsub : PowerSeriesIntegral (C4K (K := K) ^ 3 - C6K (K := K) ^ 2) :=
    integral_sub h4 h6
  have hC : PowerSeriesIntegral (PowerSeries.C ((1728 : K)⁻¹)) := by
    refine integral_C ?_
    rw [norm_inv, h1728, inv_one]
  rw [DK, generalPSEval_mul _ _ hsub hC hq,
    generalPSEval_sub _ _ h4 h6 hq,
    eval_C4K_pow_three (K := K) hint hq,
    eval_C6K_pow_two (K := K) hint hq,
    generalPSEval_C]

theorem generalPSEval_DK_eq_delta_closed (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (h1728 : ‖(1728 : K)‖ = 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (DK (K := K)) q = (TateCurve.weierstrassCurve K q).Δ := by
  rw [eval_DK (K := K) hint h1728 hq,
    eval_C4K_pow_three (K := K) hint hq,
    eval_C6K_pow_two (K := K) hint hq,
    generalPSEval_C4K_eq_c4_closed hint hq,
    generalPSEval_C6K_eq_c6_closed hint hq,
    ← LeanFormal.IUT.TateCurve.canonical_c_relation]
  have h1728ne : (1728 : K) ≠ 0 := by norm_num
  field_simp [h1728ne]

end LeanFormal.IUT.PAdicAnalytic.General
