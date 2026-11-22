import Mathlib

/-!
# Mzk1EstimateChainActual — elementary estimate chains (genuine Mathlib proofs)

Status: PENDING-VERIFY. No sorry, no axiom.
Genuine chained inequalities used by height/volume estimates. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1EstimateChainActual

/-- Genuine: four-term chained inequality. -/
theorem chain_le_four {a b c d : ℚ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d :=
  le_trans hab (le_trans hbc hcd)

/-- Genuine: adding inequalities. -/
theorem add_le_add_law {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  add_le_add hab hcd

/-- Genuine: multiplying a nonnegative term preserves the inequality. -/
theorem mul_le_mul_of_nonneg_law {a b c : ℚ} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c :=
  mul_le_mul_of_nonneg_right h hc

end LeanFormal.IUT.XiFPaper.Mzk1EstimateChainActual
