import Mathlib

/-!
# Mzk1MulBoundChainConsumerActual — chained multiplication bound consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumer: bounds multiply under nonnegativity (combine mul_le_mul with order transitivity). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1MulBoundChainConsumerActual

/-- Chained: a ≤ b, c ≤ d, 0 ≤ a, 0 ≤ c implies a * c ≤ b * d. -/
theorem mul_le_mul_chain {a b c d : ℚ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) : a * c ≤ b * d :=
  mul_le_mul hab hcd hc (le_trans ha hab)

/-- Chained: squaring preserves order on nonnegative rationals. -/
theorem sq_le_sq_chain {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  mul_le_mul hab hab ha (le_trans ha hab)

end LeanFormal.IUT.XiFPaper.Mzk1MulBoundChainConsumerActual
