import Mathlib

/-!
# Mzk1FinsetProdChainConsumerActual — chained finite-product consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers combining Finset product laws into new conclusions. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinsetProdChainConsumerActual

/-- Chained: two-step product monotonicity for nonnegative factors. -/
theorem prod_chain_le {α : Type*} (s : Finset α) (f g h : α → ℚ)
    (hf : ∀ x ∈ s, 0 ≤ f x) (hfg : ∀ x ∈ s, f x ≤ g x) (hgh : ∀ x ∈ s, g x ≤ h x) :
    (∏ x in s, f x) ≤ ∏ x in s, h x :=
  le_trans (Finset.prod_le_prod hf hfg) (Finset.prod_le_prod (fun x hx => le_trans (hf x hx) (hfg x hx)) hgh)

/-- Chained: pointwise positive products are positive. -/
theorem prod_pos_chain {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, 0 < f x) : 0 < ∏ x in s, f x :=
  Finset.prod_pos h

/-- Chained: pointwise nonnegative products are nonnegative. -/
theorem prod_nonneg_chain {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, 0 ≤ f x) : 0 ≤ ∏ x in s, f x :=
  Finset.prod_nonneg h

end LeanFormal.IUT.XiFPaper.Mzk1FinsetProdChainConsumerActual
