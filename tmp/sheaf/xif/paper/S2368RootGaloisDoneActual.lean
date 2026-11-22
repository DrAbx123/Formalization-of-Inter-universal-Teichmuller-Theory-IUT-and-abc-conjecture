import tmp.sheaf.xif.paper.S2345RootSetEquivActual
import tmp.sheaf.xif.paper.S2361SmulActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual
open LeanFormal.IUT.XiFPaper.S2361SmulActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
namespace LeanFormal.IUT.XiFPaper.S2368RootGaloisDoneActual
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
section
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
/-- Ambient compatibility: algebraMap O_L L commutes with the Galois action. -/
theorem s2368_algebraMap_smul (sigma : Gal(L/K)) (a : RingOfIntegers L) :
    algebraMap (RingOfIntegers L) L (sigma • a) =
      sigma (algebraMap (RingOfIntegers L) L a) :=
  S2361_algebraMap_smul sigma a
/-- The root-set equivalence sends the Galois action on O_L-roots to the
rootPerm action on L-roots. -/
theorem s2368_rootTransport (f : (RingOfIntegers K)[X]) (hmonic : f.Monic)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K)) (a : f.rootSet (RingOfIntegers L)) :
    ((s2345RootSetEquiv (K := K) (L := L) f hmonic).symm
      (rootPerm K L f hsplit sigma
        ((s2345RootSetEquiv (K := K) (L := L) f hmonic) a))).1 =
      sigma • a.1 := by
  apply RingOfIntegers.coe_injective
  have hval := congrArg (fun z : (s2345P f).rootSet L => (z.1 : L))
    ((s2345RootSetEquiv (K := K) (L := L) f hmonic).apply_symm_apply
      (rootPerm K L f hsplit sigma
        ((s2345RootSetEquiv (K := K) (L := L) f hmonic) a)))
  rw [← s2345RootSetEquiv_apply (K := K) (L := L) f hmonic
    ((s2345RootSetEquiv (K := K) (L := L) f hmonic).symm
      (rootPerm K L f hsplit sigma
        ((s2345RootSetEquiv (K := K) (L := L) f hmonic) a)))]
  rw [hval]
  rw [show ((rootPerm K L f hsplit sigma
      ((s2345RootSetEquiv (K := K) (L := L) f hmonic) a)).1 : L) =
      sigma • (((s2345RootSetEquiv (K := K) (L := L) f hmonic) a).1 : L) from rfl]
  rw [s2345RootSetEquiv_apply]
  exact (S2361_algebraMap_smul sigma a.1).symm
end
#print axioms s2368_algebraMap_smul
#print axioms s2368_rootTransport
end LeanFormal.IUT.XiFPaper.S2368RootGaloisDoneActual
end
