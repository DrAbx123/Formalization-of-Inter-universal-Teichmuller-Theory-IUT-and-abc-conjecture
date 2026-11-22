import tmp.sheaf.xif.paper.S2345RootSetEquivActual
import Mathlib.RingTheory.Invariant.Galois

noncomputable section
open Polynomial NumberField

namespace TestSmul4

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

section
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)

example (sigma : Gal(L/K)) (a : RingOfIntegers L) :
    sigma • a = (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma a := by
  rfl

example (sigma : Gal(L/K)) (a : RingOfIntegers L) :
    algebraMap (RingOfIntegers L) L (sigma • a) =
      sigma (algebraMap (RingOfIntegers L) L a) := by
  rw [show sigma • a = (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma a from rfl]
  exact algebraMap_galRestrict_apply (RingOfIntegers K) sigma a

end

end TestSmul4
