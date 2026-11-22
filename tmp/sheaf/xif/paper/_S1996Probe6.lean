import Mathlib.Algebra.Group.Basic

def myCommGroup (M : Type) [CommGroup M] (c : M) : CommGroup M where
  mul x y := x * c⁻¹ * y
  one := c
  inv x := c * x⁻¹ * c
  mul_assoc x y z := by simp [mul_assoc]
  one_mul x := by simp
  mul_one x := by simp
  mul_left_inv x := by simp
  mul_comm x y := by simp [mul_comm, mul_left_comm, mul_assoc]

example (M : Type) [CommGroup M] (c : M) : CommGroup M := myCommGroup M c
