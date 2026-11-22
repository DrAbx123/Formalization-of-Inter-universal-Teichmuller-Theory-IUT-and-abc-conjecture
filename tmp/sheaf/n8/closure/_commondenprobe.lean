import Mathlib
open scoped BigOperators
noncomputable section
namespace ProbeCommonDenom
variable {p : Nat} [Fact p.Prime]
variable {n : Type*} [Fintype n]
theorem common_denominator (c : n → ℚ_[p]) :
    ∃ N : ℕ, ∀ i : n, ‖(p : ℚ_[p]) ^ N * c i‖ ≤ 1 := by
  classical
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have ht := tendsto_pow_atTop_atTop_of_one_lt hp1
  have hex : ∀ i : n, ∃ N : ℕ, ‖c i‖ ≤ (p : ℝ) ^ N := by
    intro i
    exact (ht.eventually (Filter.eventually_ge_atTop (‖c i‖))).exists
  choose N_i hN_i using hex
  let N : ℕ := ∑ i, N_i i
  refine ⟨N, fun i => ?_⟩
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
  have hNiN : N_i i ≤ N := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp1
  have hpow : (p : ℝ) ^ (N_i i) ≤ (p : ℝ) ^ N :=
    pow_le_pow_right₀ (le_of_lt hp1) hNiN
  have hbound : ‖c i‖ ≤ (p : ℝ) ^ N := le_trans (hN_i i) hpow
  have hpos : (0 : ℝ) < (p : ℝ) ^ N := pow_pos hp0 N
  rw [inv_mul_le_iff₀ hpos]
  simpa using hbound
end ProbeCommonDenom
