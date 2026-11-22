import LeanFormal.IUT.Foundations.Theta.OddTheta

set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.IUT.Foundations.Theta

universe u
variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- Quadratic exponential decay for the shifted exponent n(n-1)/2 (the
negative half of the theta series). -/
theorem tendsto_quadraticExponential_mul_geometric_neg
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 < b) :
    Filter.Tendsto (fun n : ℕ => a ^ (n * (n - 1) / 2) * b ^ n)
      Filter.atTop (nhds 0) := by
  have ha_le_one : a ≤ 1 := le_of_lt ha1
  have hlim : Filter.Tendsto (fun m : ℕ => a ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  have hpos : (0 : ℝ) < 1 / (b + 1) := by
    apply one_div_pos.mpr
    linarith
  have hev : ∀ᶠ m : ℕ in Filter.atTop, a ^ m < 1 / (b + 1) :=
    hlim.eventually (isOpen_Iio.mem_nhds hpos)
  obtain ⟨m, hm⟩ := hev.exists
  have hm_lt : a ^ m * b < 1 := by
    have hb1 : (0 : ℝ) < b + 1 := by linarith
    have h1 : a ^ m * b < (1 / (b + 1)) * b :=
      mul_lt_mul_of_pos_right hm hb
    have h2 : (1 / (b + 1)) * b < 1 := by
      rw [one_div, inv_mul_eq_div]
      rw [div_lt_one hb1]
      linarith
    exact lt_trans h1 h2
  have hbase : 0 ≤ a ^ m * b := mul_nonneg (pow_nonneg ha0 m) hb.le
  have hg : Filter.Tendsto (fun n : ℕ => (a ^ m * b) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase hm_lt
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards with n
    exact mul_nonneg (pow_nonneg ha0 _) (pow_nonneg hb.le n)
  · filter_upwards [Filter.eventually_ge_atTop (2 * m + 1)] with n hn
    have hmn : m * n ≤ n * (n - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have hn1 : 1 ≤ n := by omega
      have hreal : ((m * n * 2 : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
        have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub hn1]
          norm_num
        push_cast
        rw [hncast]
        have hnreal : (2 * m + 1 : ℕ) ≤ n := hn
        have h2m : (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) - 1 := by
          have : (2 * m : ℕ) + 1 ≤ n := hnreal
          have hcast : (2 * (m : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast this
          linarith
        have hnonneg : 0 ≤ (n : ℝ) - 2 * (m : ℝ) := by linarith
        nlinarith [mul_nonneg hnonneg (show (0:ℝ) ≤ (n:ℝ) by positivity)]
      exact_mod_cast hreal
    have hpow : a ^ (n * (n - 1) / 2) ≤ a ^ (m * n) :=
      pow_le_pow_of_le_one ha0 ha_le_one hmn
    calc a ^ (n * (n - 1) / 2) * b ^ n
        ≤ a ^ (m * n) * b ^ n := by
          exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hb.le n)
      _ = (a ^ m * b) ^ n := by
          rw [mul_pow, ← pow_mul]




/-- The theta exponent at -(n+1) equals the theta exponent at n. -/
theorem oddThetaExponent_neg_succ (n : ℕ) :
    oddThetaExponent (-((n : ℤ) + 1)) = oddThetaExponent (n : ℤ) := by
  apply Nat.cast_injective (R := ℤ)
  rw [oddThetaExponent_coe, oddThetaExponent_coe]
  ring_nf

/-- The sign at -(n+1) is minus the sign at n. -/
theorem oddThetaSign_neg_succ (n : ℕ) :
    oddThetaSign (L := L) (-((n : ℤ) + 1)) = - oddThetaSign (n : ℤ) := by
  rw [oddThetaSign_eq_pow, oddThetaSign_eq_pow]
  have hself : ∀ k : ℤ, (((-1 : L) ^ k)⁻¹) = (-1 : L) ^ k := by
    intro k
    apply inv_eq_of_mul_eq_one_right
    rw [← zpow_add₀ (by norm_num : (-1 : L) ≠ 0), show k + k = 2 * k by ring,
      zpow_mul]
    norm_num
  have hsplit : -((n : ℤ) + 1) = (-(n : ℤ)) - 1 := by ring
  rw [hsplit, zpow_sub_one₀ (by norm_num : (-1 : L) ≠ 0), zpow_neg, hself n]
  norm_num

/-- The negative-index power of U in the theta term is the inverse power. -/
theorem oddThetaTerm_neg_succ (q U : L) (n : ℕ) :
    oddThetaTerm q U (-((n : ℤ) + 1)) = - oddThetaTerm q U⁻¹ (n : ℤ) := by
  rw [oddThetaTerm, oddThetaTerm, oddThetaSign_neg_succ (L := L) n,
    oddThetaExponent_neg_succ n]
  have hexp : 2 * (-((n : ℤ) + 1)) + 1 = -(2 * (n : ℤ) + 1) := by ring
  rw [hexp, zpow_neg, inv_zpow]
  ring

/-- The backward half of the odd theta series is summable. -/
theorem summable_oddThetaTerm_neg (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => oddThetaTerm q U (-(n : ℤ))) := by
  have hUinv : U⁻¹ ≠ 0 := inv_ne_zero hU
  have hshift : Summable (fun n : ℕ => oddThetaTerm q U (-((n : ℤ) + 1))) := by
    have hnat := summable_oddThetaTerm_nat q U⁻¹ hUinv hq
    have hneg : Summable (fun n : ℕ => - oddThetaTerm q U⁻¹ (n : ℤ)) := hnat.neg
    simpa only [oddThetaTerm_neg_succ] using hneg
  refine (summable_nat_add_iff (f := fun n : ℕ => oddThetaTerm q U (-(n : ℤ))) 1).mp ?_
  simpa [Nat.cast_add, Nat.cast_one] using hshift

end LeanFormal.IUT.Foundations.Theta

