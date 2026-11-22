import Mathlib
open Polynomial
example {F : Type*} [Field F] : NormalizationMonoid F := inferInstance
example {F : Type*} [Field F] [DecidableEq F] : NormalizationMonoid F[X] := inferInstance
