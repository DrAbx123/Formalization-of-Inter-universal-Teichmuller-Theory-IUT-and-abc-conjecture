import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

example : AddLeftCancelMonoid ℝ≥0 := inferInstance
example (a b : ℝ≥0) (h : a + b = 0) : a = 0 := by
  have hle : a ≤ 0 := by simpa [h] using le_add_right a b
  exact le_antisymm hle (zero_le a)
example (a b : ℝ≥0) (h : a + b = 0) : b = 0 := by
  have hle : b ≤ 0 := by simpa [add_comm a b, h] using le_add_right b a
  exact le_antisymm hle (zero_le b)
example (a b c : ℝ≥0) (h : a + b = a + c) : b = c := add_left_cancel h
example (a b : ℝ≥0) : a - b = 0 ↔ a ≤ b := tsub_eq_zero_iff_le
#check add_tsub_cancel_of_le
#check tsub_add_cancel_of_le
#check NNReal.coe_sub
#check Real.coe_toNNReal'
#check Real.toNNReal_of_nonneg
#check Real.toNNReal_of_nonpos
#check nsmul_nonneg_iff
#check nsmul_nonpos_iff
