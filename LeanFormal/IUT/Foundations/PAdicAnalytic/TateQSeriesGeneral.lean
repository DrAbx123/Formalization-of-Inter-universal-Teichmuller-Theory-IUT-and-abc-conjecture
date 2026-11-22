import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic
import LeanFormal.IUT.Foundations.PAdicAnalytic.PowerSeriesInvIntegral

open scoped ArithmeticFunction.sigma
open ArithmeticFunction PowerSeries

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic.General

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]
  (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
  (h1728 : ‖(1728 : K)‖ = 1)

noncomputable def sigmaCoeff (k n : ℕ) : K :=
  if n = 0 then 0 else (σ k n : K)

noncomputable def S3K : PowerSeries K := PowerSeries.mk (sigmaCoeff (K := K) 3)
noncomputable def S5K : PowerSeries K := PowerSeries.mk (sigmaCoeff (K := K) 5)

noncomputable def C4K : PowerSeries K :=
  1 + PowerSeries.C (240 : K) * S3K (K := K)
noncomputable def C6K : PowerSeries K :=
  -1 + PowerSeries.C (504 : K) * S5K (K := K)

noncomputable def DK : PowerSeries K :=
  (C4K (K := K) ^ 3 - C6K (K := K) ^ 2) * PowerSeries.C ((1728 : K)⁻¹)

noncomputable def HK : PowerSeries K :=
  DK (K := K) * PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1

@[simp] theorem coeff_sigmaCoeff_zero (k : ℕ) : sigmaCoeff (K := K) k 0 = 0 := by
  simp [sigmaCoeff]

@[simp] theorem coeff_S3K_zero : PowerSeries.coeff 0 (S3K (K := K)) = 0 := by
  simp [S3K]

@[simp] theorem coeff_S5K_zero : PowerSeries.coeff 0 (S5K (K := K)) = 0 := by
  simp [S5K]

theorem coeff_S3K_one : PowerSeries.coeff 1 (S3K (K := K)) = 1 := by
  simp [S3K, sigmaCoeff, ArithmeticFunction.sigma_apply]

theorem coeff_S5K_one : PowerSeries.coeff 1 (S5K (K := K)) = 1 := by
  simp [S5K, sigmaCoeff, ArithmeticFunction.sigma_apply]

@[simp] theorem coeff_C4K_zero : PowerSeries.coeff 0 (C4K (K := K)) = 1 := by
  simp [C4K, S3K, sigmaCoeff]

theorem coeff_C4K_one : PowerSeries.coeff 1 (C4K (K := K)) = 240 := by
  simp [C4K, S3K, sigmaCoeff, ArithmeticFunction.sigma_apply]

@[simp] theorem coeff_C6K_zero : PowerSeries.coeff 0 (C6K (K := K)) = -1 := by
  simp [C6K, S5K, sigmaCoeff]

theorem coeff_C6K_one : PowerSeries.coeff 1 (C6K (K := K)) = 504 := by
  simp [C6K, S5K, sigmaCoeff, ArithmeticFunction.sigma_apply]

lemma coeff_zero_mul (f g : PowerSeries K) :
    PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul]
  simp [Finset.Nat.antidiagonal_zero]

lemma coeff_one_mul (f g : PowerSeries K) :
    PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [Finset.Nat.antidiagonal_zero, add_comm, add_left_comm, add_assoc]

theorem coeff_C4K_sq_zero : PowerSeries.coeff 0 (C4K (K := K) ^ 2) = 1 := by
  rw [pow_two, coeff_zero_mul, coeff_C4K_zero]; ring

theorem coeff_C4K_sq_one : PowerSeries.coeff 1 (C4K (K := K) ^ 2) = 480 := by
  rw [pow_two, coeff_one_mul, coeff_C4K_zero, coeff_C4K_one]; ring

theorem coeff_C4K_cube_zero : PowerSeries.coeff 0 (C4K (K := K) ^ 3) = 1 := by
  rw [show C4K (K := K) ^ 3 = C4K (K := K) ^ 2 * C4K (K := K) by ring]
  rw [coeff_zero_mul, coeff_C4K_sq_zero, coeff_C4K_zero]; ring

theorem coeff_C4K_cube_one : PowerSeries.coeff 1 (C4K (K := K) ^ 3) = 720 := by
  rw [show C4K (K := K) ^ 3 = C4K (K := K) ^ 2 * C4K (K := K) by ring]
  rw [coeff_one_mul, coeff_C4K_sq_zero, coeff_C4K_sq_one,
    coeff_C4K_zero, coeff_C4K_one]; ring

theorem coeff_C6K_sq_zero : PowerSeries.coeff 0 (C6K (K := K) ^ 2) = 1 := by
  rw [pow_two, coeff_zero_mul, coeff_C6K_zero]; ring

theorem coeff_C6K_sq_one : PowerSeries.coeff 1 (C6K (K := K) ^ 2) = -1008 := by
  rw [pow_two, coeff_one_mul, coeff_C6K_zero, coeff_C6K_one]; ring

theorem coeff_D_num_zero :
    PowerSeries.coeff 0 (C4K (K := K) ^ 3 - C6K (K := K) ^ 2) = 0 := by
  have h4 : (PowerSeries.constantCoeff (C4K (K := K))) ^ 3 = 1 := by
    simpa [map_pow, PowerSeries.constantCoeff] using coeff_C4K_cube_zero (K := K)
  have h6 : (PowerSeries.constantCoeff (C6K (K := K))) ^ 2 = 1 := by
    simpa [map_pow, PowerSeries.constantCoeff] using coeff_C6K_sq_zero (K := K)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, map_pow, map_pow, h4, h6]
  ring

theorem coeff_D_num_one :
    PowerSeries.coeff 1 (C4K (K := K) ^ 3 - C6K (K := K) ^ 2) = 1728 := by
  simp [coeff_C4K_cube_one, coeff_C6K_sq_one]
  norm_num

theorem coeff_DK_zero : PowerSeries.coeff 0 (DK (K := K)) = 0 := by
  rw [DK, coeff_zero_mul, coeff_D_num_zero]; ring

theorem coeff_DK_one : PowerSeries.coeff 1 (DK (K := K)) = 1 := by
  rw [DK, coeff_one_mul, coeff_D_num_zero, coeff_D_num_one]
  simp

theorem coeff_HK_zero : PowerSeries.coeff 0 (HK (K := K)) = 0 := by
  rw [HK, coeff_zero_mul, coeff_DK_zero]; ring

theorem coeff_HK_one : PowerSeries.coeff 1 (HK (K := K)) = 1 := by
  rw [HK, coeff_one_mul, coeff_DK_zero, coeff_DK_one]
  have h0 : PowerSeries.coeff 0
      (PowerSeries.invOfUnit (C4K (K := K) ^ 3) 1) = 1 := by
    rw [PowerSeries.coeff_invOfUnit]; simp
  rw [h0]; ring

theorem HK_sub_X_dvd_X_sq :
    (PowerSeries.X : PowerSeries K) ^ 2 ∣ (HK (K := K) - PowerSeries.X) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · have hHK : PowerSeries.constantCoeff (HK (K := K)) = 0 := by
      simpa [PowerSeries.constantCoeff] using coeff_HK_zero (K := K)
    have hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
    simp [hHK, hX]
  · simp [PowerSeries.coeff_X, coeff_HK_one]


noncomputable def HRK : PowerSeries K :=
  Classical.choose (HK_sub_X_dvd_X_sq (K := K))

theorem HK_eq_X_add_Xsq_mul_HRK :
    HK (K := K) = PowerSeries.X + PowerSeries.X ^ 2 * HRK (K := K) := by
  have h := Classical.choose_spec (HK_sub_X_dvd_X_sq (K := K))
  change HK (K := K) = PowerSeries.X + PowerSeries.X ^ 2 *
    Classical.choose (HK_sub_X_dvd_X_sq (K := K))
  rw [← h]
  ring



/-! ## Task B: coefficient integrality -/

def PowerSeriesIntegral (f : PowerSeries K) : Prop :=
  ∀ n : ℕ, ‖PowerSeries.coeff n f‖ ≤ 1

lemma integral_zero : PowerSeriesIntegral (K := K) 0 := by
  intro n; simp

lemma integral_one : PowerSeriesIntegral (K := K) 1 := by
  intro n; by_cases hn : n = 0 <;> simp [PowerSeriesIntegral, hn]

lemma integral_add {f g : PowerSeries K}
    (hf : PowerSeriesIntegral f) (hg : PowerSeriesIntegral g) :
    PowerSeriesIntegral (f + g) := by
  intro n
  change ‖(PowerSeries.coeff n) (f + g)‖ ≤ 1
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

lemma integral_neg {f : PowerSeries K} (hf : PowerSeriesIntegral f) :
    PowerSeriesIntegral (-f) := by
  intro n
  change ‖(PowerSeries.coeff n) (-f)‖ ≤ 1
  rw [map_neg, norm_neg]
  exact hf n

lemma integral_sub {f g : PowerSeries K}
    (hf : PowerSeriesIntegral f) (hg : PowerSeriesIntegral g) :
    PowerSeriesIntegral (f - g) := by
  rw [sub_eq_add_neg]
  exact integral_add hf (integral_neg hg)

lemma integral_C {a : K} (ha : ‖a‖ ≤ 1) :
    PowerSeriesIntegral (PowerSeries.C a) := by
  intro n
  by_cases hn : n = 0
  · subst hn; simp; exact ha
  · simp [PowerSeries.coeff_C, hn]

lemma integral_mul {f g : PowerSeries K}
    (hf : PowerSeriesIntegral f) (hg : PowerSeriesIntegral g) :
    PowerSeriesIntegral (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (C := (1 : ℝ)) (by norm_num) ?_
  rintro ⟨i, j⟩ hij
  rw [norm_mul]
  exact mul_le_one₀ (hf i) (norm_nonneg _) (hg j)

lemma integral_pow {f : PowerSeries K} (hf : PowerSeriesIntegral f) (n : ℕ) :
    PowerSeriesIntegral (f ^ n) := by
  induction n with
  | zero => simpa using integral_one (K := K)
  | succ n ih => rw [pow_succ]; exact integral_mul ih hf

lemma integral_invOfUnit (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {f : PowerSeries K} (hf : PowerSeriesIntegral f)
    (hconst : PowerSeries.constantCoeff f = 1) :
    PowerSeriesIntegral (PowerSeries.invOfUnit f 1) := by
  intro n
  have h0 : ‖PowerSeries.coeff 0 f‖ = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hconst]
    norm_num
  exact LeanFormal.IUT.PAdicAnalytic.powerSeries_invOfUnit_coeff_norm_le_one
    hint f h0 hf n

lemma integral_S3K (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    PowerSeriesIntegral (S3K (K := K)) := by
  intro n
  by_cases hn : n = 0
  · subst hn; simp
  · simp [S3K, sigmaCoeff, hn]
    exact hint (σ 3 n)

lemma integral_S5K (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    PowerSeriesIntegral (S5K (K := K)) := by
  intro n
  by_cases hn : n = 0
  · subst hn; simp
  · simp [S5K, sigmaCoeff, hn]
    exact hint (σ 5 n)

lemma integral_C4K (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    PowerSeriesIntegral (C4K (K := K)) := by
  rw [C4K]
  exact integral_add integral_one (integral_mul (integral_C (hint 240)) (integral_S3K hint))

lemma integral_C6K (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    PowerSeriesIntegral (C6K (K := K)) := by
  rw [C6K]
  exact integral_add (integral_neg integral_one)
    (integral_mul (integral_C (hint 504)) (integral_S5K hint))

lemma integral_DK (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (h1728 : ‖(1728 : K)‖ = 1) :
    PowerSeriesIntegral (DK (K := K)) := by
  rw [DK]
  refine integral_mul (integral_sub (integral_pow (integral_C4K hint) 3)
    (integral_pow (integral_C6K hint) 2)) (integral_C ?_)
  rw [norm_inv, h1728, inv_one]

lemma integral_HK (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (h1728 : ‖(1728 : K)‖ = 1) :
    PowerSeriesIntegral (HK (K := K)) := by
  rw [HK]
  have hc4 : PowerSeries.constantCoeff (C4K (K := K)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_C4K_zero (K := K)
  exact integral_mul (integral_DK hint h1728)
    (integral_invOfUnit hint (integral_pow (integral_C4K hint) 3) (by
      rw [map_pow, hc4]
      norm_num))

theorem HK_coeff_norm_le_one (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (h1728 : ‖(1728 : K)‖ = 1) (n : ℕ) :
    ‖PowerSeries.coeff n (HK (K := K))‖ ≤ 1 :=
  integral_HK hint h1728 n


end
end LeanFormal.IUT.PAdicAnalytic.General
