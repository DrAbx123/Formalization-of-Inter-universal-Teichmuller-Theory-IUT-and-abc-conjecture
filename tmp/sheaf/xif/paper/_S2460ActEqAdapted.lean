import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
open Polynomial NumberField
variable (K L : Type) [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
example : (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp K L : MulSemiringAction Gal(L/K) (RingOfIntegers L)) = RingOfIntegers.instMulSemiringAction L := by rfl
example : (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp K L : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L)) = RingOfIntegers.instSMulCommClass L := by rfl
