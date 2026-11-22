import Mathlib
#check toAdd_mul
#check toAdd_one
example {h : Multiplicative ℤ} (hh : h ^ 2 = 1) : h = 1 := by
  rw [pow_two] at hh
  have hh' := congrArg Multiplicative.toAdd hh
  rw [toAdd_mul, toAdd_one] at hh'
  have hzero : Multiplicative.toAdd h = 0 := by omega
  exact Multiplicative.toAdd.injective hzero
