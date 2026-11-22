import tmp.sheaf.xif.paper.S1892PullbackFiniteEtaleActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1892PullbackFiniteEtaleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2541FiniteEtaleTransportEqActual

/-- Trivial equality case of finite-etale transport: equality of stack morphisms. -/
theorem S2541FiniteEtaleTransportEq
    {W Z : Iut.EtaleStackOverField S1726K}
    {f g : W.Hom Z} (h : f = g) :
    Nonempty (Iut.EtaleStackFiniteEtaleMorphism f) →
      Nonempty (Iut.EtaleStackFiniteEtaleMorphism g) := by
  intro hf
  subst h
  exact hf

#check S2541FiniteEtaleTransportEq
#print axioms S2541FiniteEtaleTransportEq
end LeanFormal.IUT.XiFPaper.S2541FiniteEtaleTransportEqActual
end