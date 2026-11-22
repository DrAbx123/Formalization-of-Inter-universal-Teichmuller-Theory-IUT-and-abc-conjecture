import Mathlib.NumberTheory.NumberField.FractionalIdeal
open scoped nonZeroDivisors
variable (K : Type*) [Field K] [NumberField K]
#synth GroupWithZero (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
#synth CommGroupWithZero (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)