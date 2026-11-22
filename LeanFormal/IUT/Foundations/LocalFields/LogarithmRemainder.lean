import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Quantitative remainder of the actual local logarithm

The local inverse needed for `O_k ⊆ (p*)⁻¹ log(O_kˣ)` comes from a
contraction, not a surjectivity field. This file proves the required
nonarchimedean estimate on the actual series: on a ball of radius r≤1/2,
the remainder `log1p - id` has Lipschitz constant 2r.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open Filter
open scoped Topology

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

omit [CharZero K] [CompleteSpace K] in
/-- Nonarchimedean power differences have no Archimedean factor n. -/
theorem norm_power_difference_le (x y : K) {r : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ ‖x - y‖ * r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : x ^ (n + 1 + 1) - y ^ (n + 1 + 1) =
        x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) := by
      ring
    rw [heq]
    apply le_trans (IsUltrametricDist.norm_add_le_max _ _)
    apply max_le
    · rw [norm_mul]
      calc
        _ ≤ r * (‖x - y‖ * r ^ n) := mul_le_mul hx ih (norm_nonneg _) hr
        _ = ‖x - y‖ * r ^ (n + 1) := by ring
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy _) (norm_nonneg _)

/-- Uniform bound for all tail coefficients on r≤1/2. -/
theorem tail_majorant_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (n : ℕ) : ((n : ℝ) + 2) * r ^ (n + 1) ≤ 2 * r := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_succ]
    calc
      _ ≤ (2 * ((n : ℝ) + 2)) * r ^ (n + 1 + 1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr _)
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      _ = (((n : ℝ) + 2) * r ^ (n + 1)) * (2 * r) := by ring
      _ ≤ (2 * r) * (2 * r) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ 2 * r := mul_le_of_le_one_right (by positivity) (by linarith)

/-- The nonlinear remainder of the source logarithm. -/
def logRemainder (x : K) : K := log1p x - x

/-- Tail terms start at degree two, with the actual analytic sign. -/
def logRemainderTerm (x : K) (n : ℕ) : K := -negativeLogTerm x (n + 1)

include localNormedAlgebra in
theorem logRemainder_hasSum (x : K) (hx : ‖x‖ < 1) :
    HasSum (logRemainderTerm x) (logRemainder x) := by
  have htail := (hasSum_nat_add_iff' (f := negativeLogTerm x) 1).mpr
    (negativeLogSeries_hasSum (p := p) x hx)
  simp only [Finset.sum_range_one] at htail
  have hzero : negativeLogTerm x 0 = -x := by simp [negativeLogTerm]
  have heq : -(negativeLogSeries x - negativeLogTerm x 0) = logRemainder x := by
    rw [hzero]
    dsimp [logRemainder, log1p]
    ring
  rw [← heq]
  exact htail.neg

include localNormedAlgebra in
/-- Termwise nonarchimedean difference estimate for the nonlinear tail. -/
theorem norm_logRemainderTerm_sub_le (x y : K) {r : ℝ}
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖logRemainderTerm x n - logRemainderTerm y n‖ ≤ 2 * r * ‖x - y‖ := by
  have heq : logRemainderTerm x n - logRemainderTerm y n =
      -((-1 : K) ^ (n + 1 + 1) *
        (x ^ (n + 1 + 1) - y ^ (n + 1 + 1)) / (n + 1 + 1 : K)) := by
    simp only [logRemainderTerm, negativeLogTerm, Nat.cast_add, Nat.cast_one]
    ring
  rw [heq, norm_neg, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    div_eq_mul_inv]
  calc
    _ ≤ (‖x - y‖ * r ^ (n + 1)) * ((n : ℝ) + 2) := by
      apply mul_le_mul (norm_power_difference_le x y hr hx hy (n + 1))
      · simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
          one_add_one_eq_two] using
          (localLog_denom_norm_inv_le (K := K) (p := p) (n := n + 2) (by omega))
      · positivity
      · positivity
    _ = ‖x - y‖ * (((n : ℝ) + 2) * r ^ (n + 1)) := by ring
    _ ≤ ‖x - y‖ * (2 * r) :=
      mul_le_mul_of_nonneg_left (tail_majorant_le_two_mul hr hrhalf n) (norm_nonneg _)
    _ = 2 * r * ‖x - y‖ := mul_comm _ _

include localNormedAlgebra in
/-- The actual logarithmic remainder contracts on every closed ball r<1/2. -/
theorem norm_logRemainder_sub_le (x y : K) {r : ℝ}
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖logRemainder x - logRemainder y‖ ≤ 2 * r * ‖x - y‖ := by
  have hrone : r < 1 := by linarith
  have hs := (logRemainder_hasSum (p := p) x (hx.trans_lt hrone)).sub
    (logRemainder_hasSum (p := p) y (hy.trans_lt hrone))
  have ht := (continuous_norm.tendsto _).comp hs.tendsto_sum_nat
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  exact norm_finsetSum_le_of_le_max _ (Finset.range n) (by positivity)
    (fun i _ => norm_logRemainderTerm_sub_le (p := p) x y hr hrhalf hx hy i)

end

end LeanFormal.IUT.LocalFieldLogarithm
