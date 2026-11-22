import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesGeneral
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators
open PowerSeries

noncomputable section

namespace LeanFormal.IUT.PAdicAnalytic.General

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Evaluation of a formal power series at a point of a complete nonarchimedean
field: `f(q) = sum_n (coeff n f) * q^n`. -/
noncomputable def generalPSEval (f : PowerSeries K) (q : K) : K :=
  ∑' n : ℕ, f.coeff n * q ^ n

theorem summable_generalPSEval (f : PowerSeries K) {q : K}
    (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => f.coeff n * q ^ n := by
  have hqR : ‖(‖q‖ : ℝ)‖ < 1 := by simpa using hq
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_norm_lt_one hqR
  refine Summable.of_norm (hgeom.of_nonneg_of_le (fun n => norm_nonneg _) ?_)
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg q) n) (hf n)

theorem summable_norm_generalPSEval (f : PowerSeries K) {q : K}
    (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖f.coeff n * q ^ n‖ := by
  have hqR : ‖(‖q‖ : ℝ)‖ < 1 := by simpa using hq
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_norm_lt_one hqR
  refine hgeom.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg q) n) (hf n)

@[simp] theorem generalPSEval_zero (q : K) :
    generalPSEval (0 : PowerSeries K) q = 0 := by
  simp [generalPSEval]

@[simp] theorem generalPSEval_C (c : K) (q : K) :
    generalPSEval (PowerSeries.C c) q = c := by
  unfold generalPSEval
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_C, hn]

@[simp] theorem generalPSEval_one (q : K) :
    generalPSEval (1 : PowerSeries K) q = 1 := by
  simpa using generalPSEval_C (1 : K) q

@[simp] theorem generalPSEval_X (q : K) :
    generalPSEval (PowerSeries.X : PowerSeries K) q = q := by
  unfold generalPSEval
  rw [tsum_eq_single 1]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_X, hn]

theorem generalPSEval_add (f g : PowerSeries K) {q : K}
    (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (hg : ∀ n, ‖g.coeff n‖ ≤ 1) (hq : ‖q‖ < 1) :
    generalPSEval (f + g) q = generalPSEval f q + generalPSEval g q := by
  unfold generalPSEval
  simp only [map_add, add_mul]
  rw [Summable.tsum_add (summable_generalPSEval f hf hq)
    (summable_generalPSEval g hg hq)]

theorem generalPSEval_neg (f : PowerSeries K) (q : K) :
    generalPSEval (-f) q = -generalPSEval f q := by
  unfold generalPSEval
  simp only [map_neg, neg_mul]
  rw [tsum_neg]

theorem generalPSEval_sub (f g : PowerSeries K) {q : K}
    (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (hg : ∀ n, ‖g.coeff n‖ ≤ 1) (hq : ‖q‖ < 1) :
    generalPSEval (f - g) q = generalPSEval f q - generalPSEval g q := by
  rw [sub_eq_add_neg, generalPSEval_add f (-g) hf (fun n => by simpa using hg n) hq,
    generalPSEval_neg]
  ring

/-- Coefficients of a power of a coefficient-bounded series are still bounded by one. -/
theorem pow_coeff_bound (f : PowerSeries K) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (m : ℕ) :
    ∀ n, ‖((f ^ m).coeff n)‖ ≤ 1 := by
  induction m with
  | zero =>
      intro n
      by_cases hn : n = 0
      · subst hn; simp
      · simp [PowerSeries.coeff_one, hn]
  | succ m ih =>
      intro n
      rw [pow_succ, PowerSeries.coeff_mul]
      have hsum : ‖∑ kl ∈ Finset.antidiagonal n, (f ^ m).coeff kl.1 * f.coeff kl.2‖ ≤ 1 := by
        apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (C := (1 : ℝ))
          (by norm_num)
        intro kl hkl
        rw [norm_mul]
        exact mul_le_one₀ (ih kl.1) (norm_nonneg _) (hf kl.2)
      simpa using hsum

/-- The evaluation map is multiplicative on power series whose coefficients are
bounded by one. -/
theorem generalPSEval_mul (f g : PowerSeries K) {q : K}
    (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (hg : ∀ n, ‖g.coeff n‖ ≤ 1) (hq : ‖q‖ < 1) :
    generalPSEval (f * g) q = generalPSEval f q * generalPSEval g q := by
  let ef : ℕ → K := fun n => f.coeff n * q ^ n
  let eg : ℕ → K := fun n => g.coeff n * q ^ n
  have hfn : Summable fun n : ℕ => ‖ef n‖ :=
    summable_norm_generalPSEval f hf hq
  have hgn : Summable fun n : ℕ => ‖eg n‖ :=
    summable_norm_generalPSEval g hg hq
  have hanti :
      generalPSEval f q * generalPSEval g q =
        ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, ef kl.1 * eg kl.2 := by
    change (∑' n : ℕ, ef n) * (∑' n : ℕ, eg n) = _
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn]
  calc
    generalPSEval (f * g) q
        = ∑' n : ℕ, (f * g).coeff n * q ^ n := rfl
    _ = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, ef kl.1 * eg kl.2 := by
          apply tsum_congr
          intro n
          rw [PowerSeries.coeff_mul]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro kl hkl
          have hkl' : kl.1 + kl.2 = n := by
            simpa using (Finset.mem_antidiagonal.mp hkl)
          simp only [ef, eg]
          rw [← hkl', pow_add]
          ring
    _ = generalPSEval f q * generalPSEval g q := hanti.symm

theorem generalPSEval_pow (f : PowerSeries K) (m : ℕ) {q : K}
    (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (hq : ‖q‖ < 1) :
    generalPSEval (f ^ m) q = generalPSEval f q ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, generalPSEval_mul _ _ (pow_coeff_bound f hf m) hf hq, ih, pow_succ]


/-- Evaluator form of the formal inverse-j expansion `H = X + X^2 * HRK`:
the evaluation of qside's formal `HK` is `q` plus the remainder series. -/
theorem eval_HK_eq_q_add_remainder [CharZero K]
    (hHK : ∀ n, ‖(HK (K := K)).coeff n‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (HK (K := K)) q =
      q + ∑' n : ℕ, (HK (K := K)).coeff (n + 2) * q ^ (n + 2) := by
  let f : ℕ → K := fun n => (HK (K := K)).coeff n * q ^ n
  have hs : Summable f := summable_generalPSEval (HK (K := K)) hHK hq
  rw [generalPSEval, hs.tsum_eq_zero_add]
  have hf0 : f 0 = 0 := by
    change (HK (K := K)).coeff 0 * q ^ 0 = 0
    rw [coeff_HK_zero]
    simp
  rw [hf0, zero_add]
  have hs1 : Summable fun n : ℕ => f (n + 1) := by
    simpa using (summable_nat_add_iff 1).mpr hs
  rw [hs1.tsum_eq_zero_add]
  have hf1 : f 1 = q := by
    change (HK (K := K)).coeff 1 * q ^ 1 = q
    rw [coeff_HK_one]
    ring
  rw [hf1]


/-- The q-series remainder attached to qside's formal `HK`:
`R(q) = sum_n HK.coeff (n+2) * q^(n+2)`. -/
noncomputable def generalTateR [CharZero K] (q : K) : K :=
  ∑' n : ℕ, (HK (K := K)).coeff (n + 2) * q ^ (n + 2)

/-- Evaluated form `H(q) = q + R(q)` for qside's formal `HK`, assuming the
coefficient bound `‖HK.coeff n‖ ≤ 1`. -/
theorem eval_HK_eq_q_add_generalTateR [CharZero K]
    (hHK : ∀ n, ‖(HK (K := K)).coeff n‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (HK (K := K)) q = q + generalTateR (K := K) q := by
  simpa [generalTateR] using eval_HK_eq_q_add_remainder (K := K) hHK hq


/-- The evaluated formal remainder theorem with qside's integrality theorem
plugged in: no coefficient-bound hypothesis remains. -/
theorem eval_HK_eq_q_add_generalTateR_of_hint [CharZero K]
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (h1728 : ‖(1728 : K)‖ = 1)
    {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (HK (K := K)) q = q + generalTateR (K := K) q := by
  exact eval_HK_eq_q_add_generalTateR (K := K)
    (HK_coeff_norm_le_one (K := K) hint h1728) hq

end LeanFormal.IUT.PAdicAnalytic.General