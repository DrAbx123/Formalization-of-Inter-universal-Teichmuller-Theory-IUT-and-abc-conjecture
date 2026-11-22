import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT.PAdicAnalytic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsUltrametricDist

noncomputable section

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]

/-- Coefficient integrality of the unit power-series inverse: if all coefficients
of `f : K⟦X⟧` have norm at most one, then all coefficients of `invOfUnit f 1`
have norm at most one. -/
theorem powerSeries_invOfUnit_coeff_norm_le_one
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (f : PowerSeries K)
    (h0 : ‖f.coeff 0‖ = 1) (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ 1) :
    ∀ n : ℕ, ‖(PowerSeries.invOfUnit f 1).coeff n‖ ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [PowerSeries.coeff_invOfUnit]
      by_cases hn : n = 0
      · subst hn
        simp
      · rw [if_neg hn]
        rw [norm_mul, norm_neg]
        have h1 : ‖((↑(1 : Kˣ) : K))⁻¹‖ ≤ 1 := by simp
        have h2 : ‖∑ x ∈ Finset.antidiagonal n,
            (if x.2 < n then (PowerSeries.coeff x.1) f *
              (PowerSeries.coeff x.2) (PowerSeries.invOfUnit f 1) else 0)‖ ≤ 1 := by
          apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
            (C := 1) (by norm_num)
          intro x hx
          split_ifs with hjn
          · rw [norm_mul]
            calc
              ‖(PowerSeries.coeff x.1) f‖ *
                  ‖(PowerSeries.coeff x.2) (PowerSeries.invOfUnit f 1)‖ ≤ 1 * 1 :=
                mul_le_mul (hf x.1) (ih x.2 hjn) (norm_nonneg _) zero_le_one
              _ = 1 := by norm_num
          · simp
        simp only [Units.val_one, inv_one, norm_one, one_mul]
        exact h2
end

end LeanFormal.IUT.PAdicAnalytic
