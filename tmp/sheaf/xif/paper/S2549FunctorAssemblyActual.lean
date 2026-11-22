import tmp.sheaf.xif.paper.S2547CorrectedFunctorFullActual
import tmp.sheaf.xif.paper.S2548S2519FullyFaithfulActual
import tmp.sheaf.xif.paper.S2542FunctorFaithfulActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2542FunctorFaithfulActual
open LeanFormal.IUT.XiFPaper.S2547CorrectedFunctorFullActual
open LeanFormal.IUT.XiFPaper.S2548S2519FullyFaithfulActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S2549FunctorAssemblyActual

theorem S2549S2540Functor_full_faithful :
    S2540Functor.Full ∧ S2540Functor.Faithful :=
  ⟨S2547Functor_full, S2542Functor_faithful⟩

noncomputable def S2549S2540Functor_fullyFaithful :
    S2540Functor.FullyFaithful :=
  letI : S2540Functor.Full := S2547Functor_full
  letI : S2540Functor.Faithful := S2542Functor_faithful
  Functor.FullyFaithful.ofFullyFaithful S2540Functor

theorem S2549S2519Functor_full_faithful :
    S2519InvFunctor.Full ∧ S2519InvFunctor.Faithful :=
  ⟨S2547S2519Full, S2547S2519Faithful⟩

noncomputable def S2549S2519Functor_fullyFaithful :
    S2519InvFunctor.FullyFaithful :=
  S2548FullyFaithful

theorem S2549S2519Functor_isEquivalence
    (h : S2519InvFunctor.EssSurj) :
    S2519InvFunctor.IsEquivalence :=
  S2548IsEquivalence h

noncomputable def S2549S2519Equivalence
    (h : S2519InvFunctor.EssSurj) :
    FiniteEtaleCover S2482AffineScheme ≌
      Iut.OrbicurveFiniteEtaleCover S2482Orbicurve :=
  S2548Equivalence h

#check S2549S2540Functor_full_faithful
#check S2549S2540Functor_fullyFaithful
#check S2549S2519Functor_full_faithful
#check S2549S2519Functor_fullyFaithful
#check S2549S2519Functor_isEquivalence
#print axioms S2549S2540Functor_fullyFaithful
#print axioms S2549S2519Functor_fullyFaithful
end LeanFormal.IUT.XiFPaper.S2549FunctorAssemblyActual
end