import tmp.sheaf.xif.paper.S1685StackTwoIsoActual

-- S1689: scheme endomorphism square is actual; stack TwoIso/nonidentity
-- remain the exact first missing lemma for S1674StrongTransOfSchemeEndo.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1689StackTwoIsoProofActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1653OrbicurveStackLiftActual
open LeanFormal.IUT.XiFPaper.S1670OrbicurveStackLiftActual
open LeanFormal.IUT.XiFPaper.S1674StackStrongTransActual
open LeanFormal.IUT.XiFPaper.S1683StackInvolutionActual
open LeanFormal.IUT.XiFPaper.S1685StackTwoIsoActual

variable {l : PrimeGeFive}

/-- Actual scheme-level involution square (re-exported from S1685). -/
theorem S1689SchemeEndo_sq :
    S1670SchemeEndo (l := l) ≫ S1670SchemeEndo (l := l) =
      𝟙 (S1419AffineOver l) :=
  S1685SchemeEndo_sq (l := l)

/-- Exact first missing lemma: functoriality of the representable StrongTrans
construction on composites. -/
def S1689StrongTransFunctorialityMissing : Prop :=
  ∀ (e : S1419AffineOver l ⟶ S1419AffineOver l),
    CategoryTheory.Pseudofunctor.StrongTrans.vcomp
      (S1674StrongTransOfSchemeEndo (l := l) e)
      (S1674StrongTransOfSchemeEndo (l := l) e) =
      S1674StrongTransOfSchemeEndo (l := l) (e ≫ e)

def S1689StackLiftNonidentityRequired : Prop :=
  S1674StackLift (l := l) ≠ S1674IdentityHom (l := l)

abbrev S1689SquareTwoIsoRequired : Type 1 :=
  Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp
      (S1674StackLift (l := l)) (S1674StackLift (l := l)))
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))

abbrev S1689SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

abbrev S1689SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1689SchemeEndo_sq
#check S1689StrongTransFunctorialityMissing
#check S1689StackLiftNonidentityRequired
#check S1689SquareTwoIsoRequired
#check S1689SignActionRequired
#check S1689SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1689StackTwoIsoProofActual

end