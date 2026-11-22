import tmp.sheaf.xif.paper.S2547CorrectedFunctorFullActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2547CorrectedFunctorFullActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2548S2519FullyFaithfulActual

instance S2548Full : S2519InvFunctor.Full := S2547S2519Full
instance S2548Faithful : S2519InvFunctor.Faithful := S2547S2519Faithful

noncomputable def S2548FullyFaithful : S2519InvFunctor.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful S2519InvFunctor

theorem S2548IsEquivalence (h : S2519InvFunctor.EssSurj) :
    S2519InvFunctor.IsEquivalence :=
  { faithful := S2547S2519Faithful
    full := S2547S2519Full
    essSurj := h }

noncomputable def S2548Equivalence (h : S2519InvFunctor.EssSurj) :
    FiniteEtaleCover S2482AffineScheme ≌
      Iut.OrbicurveFiniteEtaleCover S2482Orbicurve := by
  letI : S2519InvFunctor.IsEquivalence := S2548IsEquivalence h
  exact S2519InvFunctor.asEquivalence

#check S2548FullyFaithful
#check S2548IsEquivalence
#check S2548Equivalence
#print axioms S2548FullyFaithful
#print axioms S2548IsEquivalence
end LeanFormal.IUT.XiFPaper.S2548S2519FullyFaithfulActual
end