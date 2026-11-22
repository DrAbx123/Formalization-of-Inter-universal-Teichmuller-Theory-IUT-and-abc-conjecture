import Mathlib

/-!
# Mzk1FinsetSumPosChainActual — chained finite-sum positivity consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumer: positive terms on a nonempty finite set give a positive sum. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinsetSumPosChainActual

/-- Chained: sum of positive terms over nonempty set is positive. -/
theorem sum_pos_chain {α : Type*} (s : Finset α) (f : α → ℚ)
    (hs : s.Nonempty) (h : ∀ x ∈ s, 0 < f x) : 0 < ∑ x in s, f x :=
  Finset.sum_pos h hs

/-- Chained: nonnegative sum with one positive term is positive. -/
theorem sum_nonneg_pos_chain {α : Type*} (s : Finset α) (f : α → ℚ)
    (hx : ∃ x ∈ s, 0 < f x) (h : ∀ x ∈ s, 0 ≤ f x) : 0 < ∑ x in s, f x :=
  Finset.sum_pos_of_nonneg_of_pos h hx

end LeanFormal.IUT.XiFPaper.Mzk1FinsetSumPosChainActual
