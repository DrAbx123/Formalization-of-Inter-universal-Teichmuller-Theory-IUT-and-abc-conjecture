import tmp.sheaf.xif.paper.S1766WhiskerBridgeActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756QuotientActual
open LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoActual
open LeanFormal.IUT.XiFPaper.S1762OverModelHomActual
open LeanFormal.IUT.XiFPaper.S1766WhiskerBridgeActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1767OverToQuotConditionalActual

variable {A B : S1728Cover}

noncomputable def S1767CandidateMap (g : S1762ModelHomOver A B) :
    S1755Source A ⟶ S1755Source B :=
  Pseudofunctor.StrongTrans.vcomp (S1755ModelSectionLift A)
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K) g.hom)
      (S1755BaseChange B).toSource)

/-- The exact remaining compatibility datum for the inverse direction. -/
structure S1767CommutesData (g : S1762ModelHomOver A B) where
  commutes : Iso
    (Pseudofunctor.StrongTrans.vcomp (S1767CandidateMap g) B.map)
    A.map

noncomputable def S1767OverToQuotOfCommutes
    (g : S1762ModelHomOver A B) (c : S1767CommutesData g) :
    S1756CoverMapQuot A B :=
  Quot.mk _
    { map := S1767CandidateMap g
      commutes := c.commutes }

/-- Exact target: construct S1767CommutesData from the over-base datum. -/
def S1767CommutesConstruction : Prop :=
  forall (A B : S1728Cover) (g : S1762ModelHomOver A B),
    Nonempty (S1767CommutesData g)

#print axioms S1767OverToQuotOfCommutes

end LeanFormal.IUT.XiFPaper.S1767OverToQuotConditionalActual
end
