import Mathlib
example {K : Type*} [NormedField K] [NormedAlgebra ℚ_[2] K] [FiniteDimensional ℚ_[2] K] : Module.Finite ℚ_[2] K := inferInstance
