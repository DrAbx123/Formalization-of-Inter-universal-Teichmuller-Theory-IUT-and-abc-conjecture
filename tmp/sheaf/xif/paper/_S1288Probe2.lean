import Mathlib
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

open NumberField

example : (InfinitePlace ℚ → ℤ) := 0
example (D : InfinitePlace ℚ → ℤ) : InfinitePlace ℚ → ℤ := -D
example (D E : InfinitePlace ℚ → ℤ) : InfinitePlace ℚ → ℤ := D + E
