import Mathlib.Data.NNReal.Basic

example : AddLeftCancelMonoid NNReal := inferInstance

example (a b : NNReal) (h : a + b = 0) : a = 0 := by
  have hle : a ≤ 0 := by
    rw [← h]
    exact le_add_right
  exact le_antisymm hle zero_le

example (a b c : NNReal) (h : a + b = a + c) : b = c := add_left_cancel h

example (a b : NNReal) (h : a ≤ b) : a + (b - a) = b := add_tsub_cancel_of_le h

example (r : Real) : ((r.toNNReal : NNReal) : Real) = max r 0 := Real.coe_toNNReal' r

example (a b : NNReal) (h : a ≤ b) : ((b - a : NNReal) : Real) = (b : Real) - (a : Real) :=
  NNReal.coe_sub h

example {x : Real} {n : Nat} (hn : n ≠ 0) : 0 ≤ n • x ↔ 0 ≤ x :=
  nsmul_nonneg_iff hn
