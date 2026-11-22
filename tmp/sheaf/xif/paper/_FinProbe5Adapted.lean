import Mathlib
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [FiniteDimensional K V]
#synth Module.Finite K V
example : Finite V := Module.finite_of_finite K
