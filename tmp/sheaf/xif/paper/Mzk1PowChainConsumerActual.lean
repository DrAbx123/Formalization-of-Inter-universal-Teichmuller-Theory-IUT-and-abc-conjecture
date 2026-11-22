import Mathlib

/-!
# Mzk1PowChainConsumerActual — chained power-order consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumer: nonnegative order is preserved by natural powers (induction on exponent). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PowChainConsumerActual

/-- Chained: 0 ≤ a, a ≤ b implies a^n ≤ b^n. -/
theorem pow_le_pow_chain {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (le_trans (pow_nonneg ha n) ih)

/-- Chained: squares of nonnegatives are ordered. -/
theorem sq_le_sq_chain2 {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  pow_le_pow_chain ha hab 2

end LeanFormal.IUT.XiFPaper.Mzk1PowChainConsumerActual
