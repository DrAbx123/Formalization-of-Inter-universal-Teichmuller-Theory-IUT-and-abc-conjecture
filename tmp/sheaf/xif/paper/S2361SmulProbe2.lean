import tmp.sheaf.xif.paper.S2345RootSetEquivActual
import Mathlib.RingTheory.Invariant.Galois

noncomputable section
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual

namespace TestSmul2

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

example (sigma : Gal(L/K)) (a : RingOfIntegers L) :
    sigma • a = (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma a := by
  letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
  rfl

end TestSmul2
