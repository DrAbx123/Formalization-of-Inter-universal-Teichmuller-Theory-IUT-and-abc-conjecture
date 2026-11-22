import Mathlib

/-!
# Mzk1EstimateChainedConsumerActual — chained estimate/order consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers combining transitivity/sum-monotonicity into new height/volume conclusions. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1EstimateChainedConsumerActual

/-- Chained: four-term height/volume comparison chain. -/
theorem height_chain_le {a b c d : ℚ} (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d :=
  le_trans h1 (le_trans h2 h3)

/-- Chained: finite sum monotonicity composed twice. -/
theorem sum_chain_le {α : Type*} (s : Finset α) (f g h : α → ℚ)
    (hfg : ∀ x ∈ s, f x ≤ g x) (hgh : ∀ x ∈ s, g x ≤ h x) :
    (∑ x in s, f x) ≤ ∑ x in s, h x :=
  le_trans (Finset.sum_le_sum hfg) (Finset.sum_le_sum hgh)

/-- Chained: product of two bounded-nonnegative factors stays nonnegative. -/
theorem mul_nonneg_chain {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) : 0 ≤ b * d :=
  mul_nonneg (le_trans ha hab) (le_trans hc hcd)

end LeanFormal.IUT.XiFPaper.Mzk1EstimateChainedConsumerActual
