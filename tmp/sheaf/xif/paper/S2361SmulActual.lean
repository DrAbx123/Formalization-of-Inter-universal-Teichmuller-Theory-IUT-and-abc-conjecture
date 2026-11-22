import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Invariant.Galois

noncomputable section
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2361SmulActual

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

section
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)

/-- The integral-closure Galois action is the restricted Galois automorphism. -/
theorem S2361_smul_eq_galRestrict (sigma : Gal(L/K)) (a : RingOfIntegers L) :
    sigma • a = (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma a := by
  rfl

/-- The integral-closure Galois action commutes with the map to L. -/
theorem S2361_algebraMap_smul (sigma : Gal(L/K)) (a : RingOfIntegers L) :
    algebraMap (RingOfIntegers L) L (sigma • a) =
      sigma (algebraMap (RingOfIntegers L) L a) := by
  rw [S2361_smul_eq_galRestrict]
  exact algebraMap_galRestrict_apply (RingOfIntegers K) sigma a

#print axioms S2361_smul_eq_galRestrict
#print axioms S2361_algebraMap_smul

end

end LeanFormal.IUT.XiFPaper.S2361SmulActual
