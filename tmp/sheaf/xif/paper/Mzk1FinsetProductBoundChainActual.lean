import Mathlib

/-!
# Mzk1FinsetProductBoundChainActual — chained finite-product bound consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumer: positive pointwise factors bounded above give positive bounded product. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinsetProductBoundChainActual

/-- Chained: positive bounded factors give positive bounded product. -/
theorem prod_bounds_chain {α : Type*} (s : Finset α) (f g : α → ℚ)
    (hf : ∀ x ∈ s, 0 < f x) (hfg : ∀ x ∈ s, f x ≤ g x) :
    0 < ∏ x in s, f x ∧ (∏ x in s, f x) ≤ ∏ x in s, g x := by
  constructor
  · exact Finset.prod_pos hf
  · exact Finset.prod_le_prod (fun x hx => le_of_lt (hf x hx)) hfg

/-- Chained: positive product inherits an upper product bound. -/
theorem prod_pos_le_chain {α : Type*} (s : Finset α) (f g : α → ℚ)
    (hf : ∀ x ∈ s, 0 < f x) (hfg : ∀ x ∈ s, f x ≤ g x) :
    0 < ∏ x in s, g x :=
  lt_of_lt_of_le (Finset.prod_pos hf) (Finset.prod_le_prod (fun x hx => le_of_lt (hf x hx)) hfg)

end LeanFormal.IUT.XiFPaper.Mzk1FinsetProductBoundChainActual
