import Mathlib

/-!
# Mzk1FinsetSumProductChainActual — chained finite sum-of-products consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumer: pointwise product bounds give sum-of-products bounds. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinsetSumProductChainActual

/-- Chained: sum of bounded products is bounded. -/
theorem sum_mul_le_chain {α : Type*} (s : Finset α) (f g F G : α → ℚ)
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x)
    (hfg : ∀ x ∈ s, f x ≤ F x) (hgh : ∀ x ∈ s, g x ≤ G x) :
    (∑ x in s, f x * g x) ≤ ∑ x in s, F x * G x :=
  Finset.sum_le_sum (fun x hx =>
    mul_le_mul (hfg x hx) (hgh x hx) (hg x hx) (le_trans (hf x hx) (hfg x hx)))

/-- Chained: product bounds applied to a finite sum of squares. -/
theorem sum_sq_le_chain {α : Type*} (s : Finset α) (f F : α → ℚ)
    (hf : ∀ x ∈ s, 0 ≤ f x) (hfg : ∀ x ∈ s, f x ≤ F x) :
    (∑ x in s, f x ^ 2) ≤ ∑ x in s, F x ^ 2 :=
  Finset.sum_le_sum (fun x hx =>
    mul_le_mul (hfg x hx) (hfg x hx) (hf x hx) (le_trans (hf x hx) (hfg x hx)))

end LeanFormal.IUT.XiFPaper.Mzk1FinsetSumProductChainActual
