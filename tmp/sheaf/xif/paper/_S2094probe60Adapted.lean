import Mathlib
open Polynomial
example {K : Type*} [Field K] (g : K[X]) : Algebra K (AdjoinRoot g) := inferInstance
example {K : Type*} [Field K] (g : K[X]) : Module K (AdjoinRoot g) := inferInstance
