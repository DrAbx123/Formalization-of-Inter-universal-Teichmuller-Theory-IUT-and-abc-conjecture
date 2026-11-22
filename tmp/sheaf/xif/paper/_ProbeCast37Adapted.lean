import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
open LeanFormal.IUT
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := by
  apply Fact.mk
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 <= b ^ 2 := sq_nonneg b
  rw [hb] at hnonneg
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg
example : (algebraMap ℚ GaussianField) 37 = 37 := by norm_num
example : (algebraMap ℚ GaussianField) 37 = 37 := by rw [AdjoinRoot.algebraMap_eq]; exact map_natCast _ 37
