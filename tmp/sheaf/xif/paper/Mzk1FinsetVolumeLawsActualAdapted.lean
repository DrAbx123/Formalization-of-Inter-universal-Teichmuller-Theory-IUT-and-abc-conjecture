import Mathlib

/-!
# Mzk1FinsetVolumeLawsActualAdapted (adapted copy, A475 reuse) — finite product/sum laws (genuine Mathlib proofs)

Status: PENDING-VERIFY. No sorry, no axiom.
Genuine Mathlib lemmas used by log-volume bookkeeping: positive products, nonnegative sums,
and monotonicity of finite sums. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FinsetVolumeLawsActualAdapted

/-- Genuine: a product of positive rationals is positive. -/
theorem prod_pos_law {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, 0 < f x) : 0 < ∏ x in s, f x :=
  Finset.prod_pos h

/-- Genuine: a sum of nonnegative rationals is nonnegative. -/
theorem sum_nonneg_law {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, 0 ≤ f x) : 0 ≤ ∑ x in s, f x :=
  Finset.sum_nonneg h

/-- Genuine: finite sums are monotone pointwise. -/
theorem sum_le_sum_law {α : Type*} (s : Finset α) (f g : α → ℚ)
    (h : ∀ x ∈ s, f x ≤ g x) : (∑ x in s, f x) ≤ ∑ x in s, g x :=
  Finset.sum_le_sum h

end LeanFormal.IUT.XiFPaper.Mzk1FinsetVolumeLawsActualAdapted
