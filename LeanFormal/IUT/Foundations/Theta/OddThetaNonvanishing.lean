import LeanFormal.IUT.Foundations.Theta.OddThetaNegativeDecay

set_option linter.unnecessarySimpa false

noncomputable section

namespace LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

theorem oddThetaExponent_one_le_of_not_mem (n : ℤ)
    (hn : n ∉ ({0, -1} : Finset ℤ)) : 1 ≤ oddThetaExponent n := by
  cases n with
  | ofNat m =>
      have hm : m ≠ 0 := by
        intro h0
        apply hn
        simp [h0]
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      have hm1 : 1 ≤ m := hmpos
      have h2 : 2 ≤ m * (m + 1) := by
        calc (2 : ℕ) = 1 * 2 := by norm_num
          _ ≤ m * (m + 1) := Nat.mul_le_mul hm1 (by omega)
      change 1 ≤ oddThetaExponent ((m : ℤ))
      rw [oddThetaExponent_natCast]
      exact Nat.succ_le_of_lt (Nat.div_pos h2 (by norm_num))
  | negSucc m =>
      have hm : m ≠ 0 := by
        intro h0
        apply hn
        simp [h0]
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm
      have h2 : 2 ≤ m * (m + 1) := by
        calc (2 : ℕ) = 1 * 2 := by norm_num
          _ ≤ m * (m + 1) := Nat.mul_le_mul hm1 (by omega)
      have hneg : oddThetaExponent (Int.negSucc m) = oddThetaExponent (m : ℤ) := by
        rw [Int.negSucc_eq]
        simpa using oddThetaExponent_neg_succ m
      rw [hneg, oddThetaExponent_natCast]
      exact Nat.succ_le_of_lt (Nat.div_pos h2 (by norm_num))

theorem oddTheta_ne_zero_at_i (q i : L) (hi : i ^ 2 = -1)
    (hq : ‖q‖ < 1) (hq_two : ‖q‖ < ‖(2 : L)‖) :
    oddTheta q i ≠ 0 := by
  classical
  have hi_ne : i ≠ 0 := by
    intro h0
    have h : (0 : L) = -1 := by simpa [h0] using hi
    have h1 : (1 : L) = 0 := by simpa using h.symm
    exact one_ne_zero h1
  have hi_norm : ‖i‖ = 1 := by
    have hsq : ‖i‖ ^ 2 = 1 := by
      rw [← norm_pow, hi, norm_neg, norm_one]
    nlinarith [norm_nonneg i]
  have hi_inv : i⁻¹ = -i := by
    have hmul : i * (-i) = 1 := by
      rw [mul_neg, ← pow_two, hi, neg_neg]
    exact inv_eq_of_mul_eq_one_right hmul
  have hsum : Summable (oddThetaTerm q i) :=
    summable_oddThetaTerm q i hi_ne hq
  let s : Finset ℤ := {0, -1}
  have hs_sum : (∑ n ∈ s, oddThetaTerm q i n) = 2 * i := by
    simp [s, oddThetaTerm_zero, oddThetaTerm_neg_one, hi_inv]
    ring
  have hterm_bound : ∀ n : {n : ℤ // n ∉ s}, ‖oddThetaTerm q i n‖ ≤ ‖q‖ := by
    intro n
    have he : 1 ≤ oddThetaExponent (n : ℤ) := oddThetaExponent_one_le_of_not_mem (n : ℤ) n.2
    have he_ne : oddThetaExponent (n : ℤ) ≠ 0 := by omega
    calc
      ‖oddThetaTerm q i n‖
          = ‖q‖ ^ oddThetaExponent (n : ℤ) * ‖i‖ ^ (2 * (n : ℤ) + 1) :=
            norm_oddThetaTerm q i n
      _ = ‖q‖ ^ oddThetaExponent (n : ℤ) := by rw [hi_norm]; simp
      _ ≤ ‖q‖ := pow_le_of_le_one (norm_nonneg q) (le_of_lt hq) he_ne
  have htail_summable : Summable (fun n : {n : ℤ // n ∉ s} => oddThetaTerm q i n) :=
    hsum.comp_injective Subtype.coe_injective
  have htail_nonempty : Nonempty {n : ℤ // n ∉ s} := by
    refine ⟨⟨1, ?_⟩⟩
    simp [s]
  haveI : Nonempty {n : ℤ // n ∉ s} := htail_nonempty
  have htail_le : ‖∑' n : {n : ℤ // n ∉ s}, oddThetaTerm q i n‖ ≤ ‖q‖ :=
    IsUltrametricDist.norm_tsum_le_of_forall_le hterm_bound
  have hdecomp : oddTheta q i = (2 * i) + ∑' n : {n : ℤ // n ∉ s}, oddThetaTerm q i n := by
    rw [oddTheta]
    have h := hsum.sum_add_tsum_compl (s := s)
    rw [hs_sum] at h
    exact h.symm
  intro hzero
  have htail_eq : (∑' n : {n : ℤ // n ∉ s}, oddThetaTerm q i n) = -(2 * i) := by
    rw [hdecomp] at hzero
    have hzero' : (∑' n : {n : ℤ // n ∉ s}, oddThetaTerm q i n) + 2 * i = 0 := by
      rw [add_comm]
      exact hzero
    exact eq_neg_of_add_eq_zero_left hzero'
  have htail_norm : ‖∑' n : {n : ℤ // n ∉ s}, oddThetaTerm q i n‖ = ‖(2 : L)‖ := by
    rw [htail_eq, norm_neg, norm_mul, hi_norm, mul_one]
  have h2pos : 0 < ‖(2 : L)‖ := lt_of_le_of_lt (norm_nonneg q) hq_two
  have hle : ‖(2 : L)‖ ≤ ‖q‖ := by
    calc ‖(2 : L)‖ = ‖∑' n : {n : ℤ // n ∉ s}, oddThetaTerm q i n‖ := htail_norm.symm
      _ ≤ ‖q‖ := htail_le
  linarith

end LeanFormal.IUT.Foundations.Theta