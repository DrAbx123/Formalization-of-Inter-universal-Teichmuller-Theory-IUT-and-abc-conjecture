import tmp.sheaf.xif.paper.S2382ArithFrobDoneActual
import tmp.sheaf.xif.paper.S2361SmulActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2574LocalizedP12Actual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596GaloisFixesCActual
open LeanFormal.IUT.XiFPaper.S2361SmulActual
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
section
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
lemma galois_fixes_algebraMap_C (sigma : Gal(L/K)) (c : RingOfIntegers K) :
    sigma • algebraMap (RingOfIntegers K) (RingOfIntegers L) c =
      algebraMap (RingOfIntegers K) (RingOfIntegers L) c := by
  apply RingOfIntegers.coe_injective
  rw [S2361_algebraMap_smul]
  rw [← IsScalarTower.algebraMap_apply (RingOfIntegers K) (RingOfIntegers L) L]
  rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L]
  exact sigma.commutes (algebraMap (RingOfIntegers K) K c)
#print axioms galois_fixes_algebraMap_C
end
end LeanFormal.IUT.XiFPaper.S2596GaloisFixesCActual
end
