import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
open Polynomial NumberField
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
example (sigma : Gal(L/K)) (alpha : RingOfIntegers L) :
    (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
      IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
     sigma • alpha) = (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma alpha := by
  rfl
