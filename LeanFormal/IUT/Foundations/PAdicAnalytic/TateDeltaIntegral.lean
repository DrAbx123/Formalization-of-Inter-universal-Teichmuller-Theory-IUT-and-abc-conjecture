import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesGeneral
import LeanFormal.IUT.Foundations.PAdicAnalytic.PowerSeriesInvIntegral
import LeanFormal.IUT.Foundations.PAdicAnalytic.GeneralPSEval
import LeanFormal.IUT.Foundations.PAdicAnalytic.TatePSEvalIdentity
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateJGeneral
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction.sigma
open ArithmeticFunction PowerSeries
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic.General

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

noncomputable def normalizedNumerator : PowerSeries K :=
  C4K (K := K) ^ 3 - C6K (K := K) ^ 2

lemma zmod12_pow_three_eq_pow_five (d : ℕ) :
    ((d ^ 3 : ℕ) : ZMod 12) = ((d ^ 5 : ℕ) : ZMod 12) := by
  have hpoly : ∀ x : ZMod 12, x ^ 3 = x ^ 5 := by decide
  simpa [Nat.cast_pow] using hpoly (d : ZMod 12)

lemma sigma_three_modEq_sigma_five (n : ℕ) :
    σ 3 n ≡ σ 5 n [MOD 12] := by
  have hcast : ((σ 3 n : ℕ) : ZMod 12) = ((σ 5 n : ℕ) : ZMod 12) := by
    rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro d hd
    exact (by simpa [Nat.cast_pow] using zmod12_pow_three_eq_pow_five d)
  exact (ZMod.natCast_eq_natCast_iff (σ 3 n) (σ 5 n) 12).mp hcast

lemma twelve_dvd_five_sigma_three_add_seven_sigma_five (n : ℕ) :
    12 ∣ 5 * σ 3 n + 7 * σ 5 n := by
  have hmod : σ 3 n ≡ σ 5 n [MOD 12] := sigma_three_modEq_sigma_five n
  have h : 5 * σ 3 n + 7 * σ 5 n ≡ 0 [MOD 12] := by
    calc
      5 * σ 3 n + 7 * σ 5 n ≡ 5 * σ 5 n + 7 * σ 5 n [MOD 12] :=
        Nat.ModEq.add (Nat.ModEq.mul_left 5 hmod) (Nat.ModEq.refl (7 * σ 5 n))
      _ = 12 * σ 5 n := by ring
      _ ≡ 0 [MOD 12] := by
        exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 12 _)
  exact Nat.modEq_zero_iff_dvd.mp h

/-- Coefficients (5 sigma_3(n)+7 sigma_5(n))/12, integral by mod-12 congruence. -/
noncomputable def sigmaDiv12 : PowerSeries K :=
  PowerSeries.mk (fun n : ℕ => ((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ))

lemma sigmaDiv12_coeff (n : ℕ) :
    PowerSeries.coeff n (sigmaDiv12 (K := K)) =
      (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : K) := by
  simp [sigmaDiv12]

lemma integral_sigmaDiv12 (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    PowerSeriesIntegral (sigmaDiv12 (K := K)) := by
  intro n
  rw [sigmaDiv12_coeff]
  exact hint _


noncomputable def firstTermK : PowerSeries K :=
  PowerSeries.C ((1 : K) / 12) *
    (PowerSeries.C (5 : K) * S3K (K := K) +
      PowerSeries.C (7 : K) * S5K (K := K))

lemma firstTermK_coeff (n : ℕ) :
    PowerSeries.coeff n (firstTermK (K := K)) =
      (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : K) := by
  have hdiv : 12 ∣ 5 * σ 3 n + 7 * σ 5 n :=
    twelve_dvd_five_sigma_three_add_seven_sigma_five n
  rw [firstTermK, PowerSeries.coeff_C_mul]
  by_cases hn : n = 0
  · subst hn
    simp [S3K, S5K, sigmaCoeff, ArithmeticFunction.sigma_apply]
  · simp [map_add, PowerSeries.coeff_C_mul, S3K, S5K, sigmaCoeff, hn]
    rw [Nat.cast_div_charZero hdiv]
    push_cast
    ring

lemma integral_firstTermK (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    PowerSeriesIntegral (firstTermK (K := K)) := by
  intro n
  rw [firstTermK_coeff]
  exact hint _

noncomputable def DeltaK : PowerSeries K :=
  firstTermK (K := K) + PowerSeries.C (100 : K) * S3K (K := K) ^ 2 +
    PowerSeries.C (8000 : K) * S3K (K := K) ^ 3 -
      PowerSeries.C (147 : K) * S5K (K := K) ^ 2

lemma integral_DeltaK (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    PowerSeriesIntegral (DeltaK (K := K)) := by
  have h100 : PowerSeriesIntegral (PowerSeries.C (100 : K)) := integral_C (hint 100)
  have h8000 : PowerSeriesIntegral (PowerSeries.C (8000 : K)) := integral_C (hint 8000)
  have h147 : PowerSeriesIntegral (PowerSeries.C (147 : K)) := integral_C (hint 147)
  unfold DeltaK
  refine integral_sub (integral_add (integral_add (integral_firstTermK hint)
    (integral_mul h100 (integral_pow (integral_S3K (K := K) hint) 2)))
    (integral_mul h8000 (integral_pow (integral_S3K (K := K) hint) 3)))
    (integral_mul h147 (integral_pow (integral_S5K (K := K) hint) 2))

lemma normalizedNumerator_eq_1728_mul_DeltaK :
    normalizedNumerator (K := K) = PowerSeries.C (1728 : K) * DeltaK (K := K) := by
  rw [normalizedNumerator, DeltaK, firstTermK]
  have hC : ∀ a b : K, PowerSeries.C a * PowerSeries.C b =
      PowerSeries.C (a * b) := fun a b => (map_mul PowerSeries.C a b).symm
  have h3 : (3 : PowerSeries K) = PowerSeries.C (3 : K) :=
    (map_natCast PowerSeries.C (3 : ℕ)).symm
  have h2 : (2 : PowerSeries K) = PowerSeries.C (2 : K) :=
    (map_natCast PowerSeries.C (2 : ℕ)).symm
  simp only [C4K, C6K]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm, ← map_mul, ← map_pow]
  ring_nf
  rw [h3, h2]
  simp only [mul_assoc, hC]
  ring

noncomputable def HKno1728 : PowerSeries K :=
  DeltaK (K := K) * PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1

theorem HKno1728_coeff_norm_le_one
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (n : ℕ) :
    ‖(HKno1728 (K := K)).coeff n‖ ≤ 1 := by
  have hDelta : PowerSeriesIntegral (DeltaK (K := K)) := integral_DeltaK hint
  have hC4 : PowerSeriesIntegral (C4K (K := K) ^ 3) :=
    integral_pow (integral_C4K (K := K) hint) 3
  have hconst : PowerSeries.constantCoeff (C4K (K := K) ^ 3) = 1 := by
    rw [map_pow]
    have hc4 : PowerSeries.constantCoeff (C4K (K := K)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact coeff_C4K_zero (K := K)
    rw [hc4]; norm_num
  have hInv : PowerSeriesIntegral (PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1) :=
    integral_invOfUnit (K := K) hint hC4 hconst
  rw [HKno1728]
  exact integral_mul hDelta hInv n

lemma DK_eq_DeltaK : DK (K := K) = DeltaK (K := K) := by
  rw [DK]
  change normalizedNumerator (K := K) * PowerSeries.C ((1728 : K)⁻¹) = DeltaK (K := K)
  rw [normalizedNumerator_eq_1728_mul_DeltaK]
  have hscalar : PowerSeries.C (1728 : K) * PowerSeries.C ((1728 : K)⁻¹) = 1 := by
    rw [← map_mul]
    field_simp
    norm_num
  calc
    (PowerSeries.C (1728 : K) * DeltaK (K := K)) *
        PowerSeries.C ((1728 : K)⁻¹) =
      (PowerSeries.C (1728 : K) * PowerSeries.C ((1728 : K)⁻¹)) *
        DeltaK (K := K) := by ring
    _ = DeltaK (K := K) := by rw [hscalar, one_mul]

lemma HKno1728_eq_HK : HKno1728 (K := K) = HK (K := K) := by
  rw [HKno1728, HK, DK_eq_DeltaK]

theorem HK_coeff_norm_le_one_no1728
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (n : ℕ) :
    ‖(HK (K := K)).coeff n‖ ≤ 1 := by
  rw [← HKno1728_eq_HK]
  exact HKno1728_coeff_norm_le_one hint n



lemma integral_DK_no1728 (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    PowerSeriesIntegral (DK (K := K)) := by
  rw [DK_eq_DeltaK]
  exact integral_DeltaK hint

theorem generalPSEval_normalizedNumerator_eq_c4_c6_no1728
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (normalizedNumerator (K := K)) q =
      (TateCurve.weierstrassCurve K q).c₄ ^ 3 -
        (TateCurve.weierstrassCurve K q).c₆ ^ 2 := by
  change generalPSEval (C4K (K := K) ^ 3 - C6K (K := K) ^ 2) q =
    (TateCurve.weierstrassCurve K q).c₄ ^ 3 -
      (TateCurve.weierstrassCurve K q).c₆ ^ 2
  rw [generalPSEval_sub _ _
    (integral_pow (integral_C4K (K := K) hint) 3)
    (integral_pow (integral_C6K (K := K) hint) 2) hq,
    generalPSEval_pow (C4K (K := K)) 3 (integral_C4K (K := K) hint) hq,
    generalPSEval_pow (C6K (K := K)) 2 (integral_C6K (K := K) hint) hq,
    generalPSEval_C4K_eq_c4_closed hint hq,
    generalPSEval_C6K_eq_c6_closed hint hq]

theorem generalPSEval_DeltaK_eq_delta_no1728
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (DeltaK (K := K)) q =
      (TateCurve.weierstrassCurve K q).Δ := by
  have hnumEval : generalPSEval (normalizedNumerator (K := K)) q =
      (TateCurve.weierstrassCurve K q).c₄ ^ 3 -
        (TateCurve.weierstrassCurve K q).c₆ ^ 2 :=
    generalPSEval_normalizedNumerator_eq_c4_c6_no1728 hint hq
  have hprod : generalPSEval
      (PowerSeries.C (1728 : K) * DeltaK (K := K)) q =
      (1728 : K) * generalPSEval (DeltaK (K := K)) q := by
    rw [generalPSEval_mul (PowerSeries.C (1728 : K)) (DeltaK (K := K))
      (integral_C (hint 1728)) (integral_DeltaK hint) hq,
      generalPSEval_C]
  have heq := congrArg (fun f : PowerSeries K => generalPSEval f q)
    (normalizedNumerator_eq_1728_mul_DeltaK (K := K))
  rw [hprod, hnumEval] at heq
  have h1728 : (1728 : K) ≠ 0 := by norm_num
  have hrelation : (1728 : K) *
      (TateCurve.weierstrassCurve K q).Δ =
      (TateCurve.weierstrassCurve K q).c₄ ^ 3 -
        (TateCurve.weierstrassCurve K q).c₆ ^ 2 :=
    TateCurve.canonical_c_relation (K := K) q
  apply mul_left_cancel₀ h1728
  rw [← heq, ← hrelation]

theorem generalPSEval_DK_eq_delta_no1728
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (DK (K := K)) q =
      (TateCurve.weierstrassCurve K q).Δ := by
  rw [DK_eq_DeltaK]
  exact generalPSEval_DeltaK_eq_delta_no1728 hint hq

lemma eval_invOfUnit_C4K_cube_no1728
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
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
  have hfi : PowerSeriesIntegral
      (PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1) :=
    integral_invOfUnit (K := K) hint hf hconst
  have hmul := congrArg (fun s : PowerSeries K => generalPSEval s q)
    (PowerSeries.mul_invOfUnit (C4K (K := K) ^ 3) 1 hconst)
  rw [generalPSEval_mul _ _ hf hfi hq, generalPSEval_one] at hmul
  exact (inv_eq_of_mul_eq_one_right hmul).symm

theorem generalPSEval_HK_eq_tateHK_no1728
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (HK (K := K)) q =
      LeanFormal.IUT.PAdicAnalytic.tateHK (K := K) q := by
  have hD : PowerSeriesIntegral (DK (K := K)) := integral_DK_no1728 hint
  have hC4 : PowerSeriesIntegral (C4K (K := K) ^ 3) :=
    integral_pow (integral_C4K (K := K) hint) 3
  have hconst : PowerSeries.constantCoeff (C4K (K := K) ^ 3) = 1 := by
    rw [map_pow]
    have hc4 : PowerSeries.constantCoeff (C4K (K := K)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact coeff_C4K_zero (K := K)
    rw [hc4]; norm_num
  have hInv : PowerSeriesIntegral
      (PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1) :=
    integral_invOfUnit (K := K) hint hC4 hconst
  rw [HK, generalPSEval_mul _ _ hD hInv hq,
    generalPSEval_DK_eq_delta_no1728 hint hq,
    eval_invOfUnit_C4K_cube_no1728 hint hq,
    generalPSEval_pow (C4K (K := K)) 3 (integral_C4K (K := K) hint) hq,
    generalPSEval_C4K_eq_c4_closed hint hq]
  rw [LeanFormal.IUT.PAdicAnalytic.tateHK, div_eq_mul_inv]



theorem tateHK_eq_q_add_generalTateR_no1728
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    LeanFormal.IUT.PAdicAnalytic.tateHK (K := K) q =
      q + generalTateR (K := K) q := by
  rw [← generalPSEval_HK_eq_tateHK_no1728 hint hq]
  exact eval_HK_eq_q_add_generalTateR (K := K)
    (HK_coeff_norm_le_one_no1728 hint) hq


end LeanFormal.IUT.PAdicAnalytic.General
