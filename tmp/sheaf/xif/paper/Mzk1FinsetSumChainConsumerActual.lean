import Mathlib

/-!
# Mzk1FinsetSumChainConsumerActual — chained finite-sum consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers combining Finset sum laws into new conclusions. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinsetSumChainConsumerActual

/-- Chained: sum of pointwise sums is the sum of sums. -/
theorem sum_add_chain {α : Type*} (s : Finset α) (f g : α → ℚ) :
    (∑ x in s, (f x + g x)) = (∑ x in s, f x) + ∑ x in s, g x :=
  Finset.sum_add_distrib

/-- Chained: two-step sum monotonicity. -/
theorem sum_chain2 {α : Type*} (s : Finset α) (f g h : α → ℚ)
    (hfg : ∀ x ∈ s, f x ≤ g x) (hgh : ∀ x ∈ s, g x ≤ h x) :
    (∑ x in s, f x) ≤ ∑ x in s, h x :=
  le_trans (Finset.sum_le_sum hfg) (Finset.sum_le_sum hgh)

/-- Chained: nonnegative sum plus nonnegative sum. -/
theorem sum_add_nonneg_chain {α : Type*} (s : Finset α) (f g : α → ℚ)
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) :
    0 ≤ (∑ x in s, f x) + ∑ x in s, g x :=
  add_nonneg (Finset.sum_nonneg hf) (Finset.sum_nonneg hg)

end LeanFormal.IUT.XiFPaper.Mzk1FinsetSumChainConsumerActual
