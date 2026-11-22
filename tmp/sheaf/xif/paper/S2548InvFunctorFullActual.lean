import tmp.sheaf.xif.paper.S2547CorrectedFullyFaithfulActual
import tmp.sheaf.xif.paper.S2542FunctorFaithfulActual
import Mathlib.CategoryTheory.EssentialImage

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
set_option backward.isDefEq.respectTransparency false
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2542FunctorFaithfulActual
open LeanFormal.IUT.XiFPaper.S2547CorrectedFullyFaithfulActual

namespace LeanFormal.IUT.XiFPaper.S2548InvFunctorFullActual

noncomputable instance S2548InvFunctor_full : S2519InvFunctor.Full :=
  CategoryTheory.Functor.full_of_comp_essSurj S2519InvFunctor
    S2538AffineCoverEquiv.inverse
    (by
      intro X1 X2 φ
      obtain ⟨f, hf⟩ := S2547Functor_full.map_surjective φ
      refine ⟨S2538AffineCoverEquiv.inverse.map f, ?_⟩
      have hf' : S2519InvFunctor.map (S2538AffineCoverEquiv.inverse.map f) = φ :=
        hf
      exact hf')

noncomputable def S2548InvFunctor_fullyFaithful :
    S2519InvFunctor.FullyFaithful :=
  letI : S2519InvFunctor.Full := S2548InvFunctor_full
  letI : S2519InvFunctor.Faithful := S2542InvFunctorFaithful
  Functor.FullyFaithful.ofFullyFaithful S2519InvFunctor

#check S2548InvFunctor_full
#check S2548InvFunctor_fullyFaithful
#print axioms S2548InvFunctor_fullyFaithful
end LeanFormal.IUT.XiFPaper.S2548InvFunctorFullActual
end