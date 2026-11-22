import tmp.sheaf.xif.paper.S2345RootSetEquivActual
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2352GaloisActionCompatActual
open Polynomial NumberField
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
/-- Galois action on O_L commutes with algebraMap O_L -> L. -/
theorem s2352_algebraMap_smul (sigma : Gal(L/K)) (alpha : RingOfIntegers L) :
    algebraMap (RingOfIntegers L) L (sigma • alpha) =
      sigma (algebraMap (RingOfIntegers L) L alpha) := by
  letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
  dsimp only [IsIntegralClosure.MulSemiringAction, MulSemiringAction.compHom]
  exact algebraMap_galRestrict_apply (RingOfIntegers K) sigma alpha
#print axioms s2352_algebraMap_smul
end LeanFormal.IUT.XiFPaper.S2352GaloisActionCompatActual
end
