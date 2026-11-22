import tmp.sheaf.xif.paper.S2549FunctorAssemblyActual
import tmp.sheaf.xif.paper.S2538AffineCoverEquivActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2549FunctorAssemblyActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2552S2540EquivalenceActual

theorem S2552S2540Functor_isEquivalence
    (h : S2519InvFunctor.EssSurj) :
    S2540Functor.IsEquivalence := by
  letI : S2519InvFunctor.IsEquivalence := S2549S2519Functor_isEquivalence h
  change (S2538AffineCoverEquiv.inverse ⋙ S2519InvFunctor).IsEquivalence
  infer_instance

noncomputable def S2552S2540Equivalence
    (h : S2519InvFunctor.EssSurj) :
    (CommAlgCat.FiniteEtale S2482CoordinateRing)ᵒᵖ ≌
      Iut.OrbicurveFiniteEtaleCover S2482Orbicurve := by
  letI : S2540Functor.IsEquivalence := S2552S2540Functor_isEquivalence h
  exact S2540Functor.asEquivalence

#check S2552S2540Functor_isEquivalence
#check S2552S2540Equivalence
#print axioms S2552S2540Functor_isEquivalence
end LeanFormal.IUT.XiFPaper.S2552S2540EquivalenceActual
end