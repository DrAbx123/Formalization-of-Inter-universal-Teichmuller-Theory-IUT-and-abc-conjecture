import tmp.sheaf.xif.paper.S2546CorrectedFullActual
import tmp.sheaf.xif.paper.S2542FunctorFaithfulActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2543CorrectedQuotMapActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.FullD3D4Agent
open LeanFormal.IUT.XiFPaper.S2542FunctorFaithfulActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2547CorrectedFunctorFullActual

theorem S2547Functor_full : S2540Functor.Full where
  map_surjective := by
    intro X Y g
    let A := Opposite.unop Y
    let B := Opposite.unop X
    obtain ⟨f, hf⟩ := S2543QuotMapRSurjective_holds (A := A) (B := B) g
    exact ⟨Quiver.Hom.op f, hf⟩

theorem S2547Functor_full_faithful :
    S2540Functor.Full ∧ S2540Functor.Faithful :=
  ⟨S2547Functor_full, S2542Functor_faithful⟩

instance S2547FunctorFullInst : S2540Functor.Full := S2547Functor_full
instance S2547FunctorFaithfulInst : S2540Functor.Faithful := S2542Functor_faithful

noncomputable def S2547Iso :
    (S2538AffineCoverEquiv.functor ⋙ S2540Functor) ≅ S2519InvFunctor :=
  (Functor.associator _ _ _).symm.trans
    ((Functor.isoWhiskerRight S2538AffineCoverEquiv.unitIso.symm S2519InvFunctor).trans
      (Functor.leftUnitor _))

theorem S2547S2519Full : S2519InvFunctor.Full :=
  Functor.Full.of_iso S2547Iso

theorem S2547S2519Faithful : S2519InvFunctor.Faithful :=
  Functor.Faithful.of_iso S2547Iso

#check S2547Functor_full
#check S2547Functor_full_faithful
#print axioms S2547Functor_full
#print axioms S2547Functor_full_faithful
end LeanFormal.IUT.XiFPaper.S2547CorrectedFunctorFullActual
end