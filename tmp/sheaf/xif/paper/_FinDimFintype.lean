import Mathlib
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [FiniteDimensional K V]
#synth Fintype V
#check @FiniteDimensional.fintype
#check @Module.fintype
#check @Fintype.ofFinite
