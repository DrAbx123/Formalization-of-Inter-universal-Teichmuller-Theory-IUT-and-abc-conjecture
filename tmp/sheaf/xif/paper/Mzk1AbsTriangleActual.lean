import Mathlib

/-!
# Mzk1AbsTriangleActual — triangle inequalities for ℚ (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Genuine triangle inequalities and finite absolute-sum bounds. -/

open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsTriangleActual

/-- Genuine theorem: triangle inequality for ℚ. -/
theorem abs_add_chain (a b : ℚ) : |a + b| ≤ |a| + |b| :=
  abs_add_le a b

/-- Genuine theorem: reverse triangle inequality. -/
theorem abs_sub_abs_le_chain (a b : ℚ) : |a| - |b| ≤ |a - b| :=
  abs_sub_abs_le_abs_sub a b

/-- Genuine theorem: absolute value of a finite sum. -/
theorem abs_sum_le_sum_abs {α : Type*} (s : Finset α) (f : α → ℚ) :
    |∑ x ∈ s, f x| ≤ ∑ x ∈ s, |f x| :=
  Finset.abs_sum_le_sum_abs s f

/-- Genuine theorem: absolute value of a product. -/
theorem abs_mul_chain (a b : ℚ) : |a * b| = |a| * |b| :=
  abs_mul a b

end LeanFormal.IUT.XiFPaper.Mzk1AbsTriangleActual
