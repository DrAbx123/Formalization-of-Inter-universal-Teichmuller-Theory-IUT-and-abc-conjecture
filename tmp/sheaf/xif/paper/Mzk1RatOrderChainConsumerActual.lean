import Mathlib

/-!
# Mzk1RatOrderChainConsumerActual — chained rational order consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers: strict/nonstrict order chains combined into new inequalities. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RatOrderChainConsumerActual

/-- Chained: strict plus nonstrict addition chain. -/
theorem add_lt_add_chain {a b c d : ℚ} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d :=
  add_lt_add_of_lt_of_le h1 h2

/-- Chained: two-step strict inequality chain. -/
theorem lt_chain2 {a b c : ℚ} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  lt_of_lt_of_le h1 h2

/-- Chained: multiplication preserves nonstrict inequality under nonnegative factor. -/
theorem mul_le_chain {a b c : ℚ} (h1 : a ≤ b) (h2 : 0 ≤ c) : a * c ≤ b * c :=
  mul_le_mul_of_nonneg_right h1 h2

end LeanFormal.IUT.XiFPaper.Mzk1RatOrderChainConsumerActual
