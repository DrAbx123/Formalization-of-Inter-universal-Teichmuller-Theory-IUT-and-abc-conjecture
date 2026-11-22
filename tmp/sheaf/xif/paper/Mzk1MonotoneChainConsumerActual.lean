import Mathlib

/-!
# Mzk1MonotoneChainConsumerActual — chained monotonicity consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers: composition/add-constant/nonnegative-scaling preserve monotonicity. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1MonotoneChainConsumerActual

/-- Chained: composition of monotone functions is monotone. -/
theorem monotone_comp_chain {f g : ℚ → ℚ} (hf : Monotone f) (hg : Monotone g) :
    Monotone (g ∘ f) :=
  hg.comp hf

/-- Chained: adding a constant preserves monotonicity. -/
theorem monotone_add_const_chain {f : ℚ → ℚ} (hf : Monotone f) (c : ℚ) :
    Monotone (fun x => f x + c) := by
  intro a b h
  exact add_le_add (hf h) le_rfl

/-- Chained: multiplying by a nonnegative constant preserves monotonicity. -/
theorem monotone_mul_nonneg_chain {f : ℚ → ℚ} (hf : Monotone f) {c : ℚ} (hc : 0 ≤ c) :
    Monotone (fun x => f x * c) := by
  intro a b h
  exact mul_le_mul_of_nonneg_right (hf h) hc

end LeanFormal.IUT.XiFPaper.Mzk1MonotoneChainConsumerActual
