import tmp.sheaf.xif.paper.S1691StrongTransFunctorialityActual

-- S1693: direct TwoIso attempt.  App-level functoriality/id are actual;
-- TwoIso currently requires a full modification/2-iso construction, recorded
-- as the exact first missing.  No fake TwoIso/signAction.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1693TwoIsoDirectActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1670OrbicurveStackLiftActual
open LeanFormal.IUT.XiFPaper.S1674StackStrongTransActual
open LeanFormal.IUT.XiFPaper.S1683StackInvolutionActual
open LeanFormal.IUT.XiFPaper.S1685StackTwoIsoActual
open LeanFormal.IUT.XiFPaper.S1691StrongTransFunctorialityActual

variable {l : PrimeGeFive}

theorem S1693App_vcomp
    (e : S1419AffineOver l ⟶ S1419AffineOver l)
    (U : LocallyDiscrete (S1674C (l := l))ᵒᵖ) :
    S1674App (l := l) e U ≫ S1674App (l := l) e U =
      S1674App (l := l) (e ≫ e) U :=
  S1691App_vcomp (l := l) e U

theorem S1693App_id (U : LocallyDiscrete (S1674C (l := l))ᵒᵖ) :
    S1674App (l := l) (𝟙 (S1419AffineOver l)) U =
      𝟙 ((S1674F (l := l)).obj U) :=
  S1691App_id (l := l) U

theorem S1693SchemeEndo_sq :
    S1670SchemeEndo (l := l) ≫ S1670SchemeEndo (l := l) =
      𝟙 (S1419AffineOver l) :=
  S1685SchemeEndo_sq (l := l)

/-- Exact first missing: the TwoIso itself. -/
abbrev S1693SquareTwoIsoRequired : Type 1 :=
  Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp
      (S1674StackLift (l := l)) (S1674StackLift (l := l)))
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))

/-- Exact first missing primitive: a modification/2-isomorphism between the
composite StrongTrans and the identity StrongTrans. -/
def S1693ModificationFirstMissing : Prop :=
  Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoCell
    (Iut.HyperbolicOrbicurve.Hom.comp
      (S1674StackLift (l := l)) (S1674StackLift (l := l)))
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l))))

def S1693StackLiftNonidentityRequired : Prop :=
  S1674StackLift (l := l) ≠ S1674IdentityHom (l := l)

abbrev S1693SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

abbrev S1693SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1693App_vcomp
#check S1693App_id
#check S1693SchemeEndo_sq
#check S1693SquareTwoIsoRequired
#check S1693ModificationFirstMissing
#check S1693StackLiftNonidentityRequired
#check S1693SignActionRequired
#check S1693SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1693TwoIsoDirectActual

end