import Mathlib
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [FiniteDimensional K V]
#synth Finite V
#check @FiniteDimensional.finite
#check @Module.finite_of_finite
