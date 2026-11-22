import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Invariant.Galois

noncomputable section
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2381SmulCommActual

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

section
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)

local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) where
  smul_comm g a b := by
    change (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) g (a • b) =
      a • (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) g b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) g |>.commutes a

theorem S2381_smulCommClass :
    SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) := inferInstance

#print axioms S2381_smulCommClass

end

end LeanFormal.IUT.XiFPaper.S2381SmulCommActual
