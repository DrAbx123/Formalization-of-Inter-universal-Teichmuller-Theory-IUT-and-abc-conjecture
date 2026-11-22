import tmp.sheaf.xif.paper.S2345RootSetEquivActual
import Mathlib.RingTheory.Invariant.Galois

noncomputable section
open Polynomial NumberField

namespace TestSmul3

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] IsIntegralClosure.MulSemiringAction

example (sigma : Gal(L/K)) (a : RingOfIntegers L) :
    algebraMap (RingOfIntegers L) L (sigma • a) =
      sigma (algebraMap (RingOfIntegers L) L a) := by
  rw [algebraMap_galRestrict_apply]

end TestSmul3
