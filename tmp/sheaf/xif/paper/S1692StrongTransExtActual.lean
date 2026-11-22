import tmp.sheaf.xif.paper.S1691StrongTransFunctorialityActual

-- S1692: app-level functoriality/id are actual; full StrongTrans ext/
-- TwoIso/nonidentity/signAction remain exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1692StrongTransExtActual

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

/-- Re-export actual app-level functoriality. -/
theorem S1692App_vcomp
    (e : S1419AffineOver l ⟶ S1419AffineOver l)
    (U : LocallyDiscrete (S1674C (l := l))ᵒᵖ) :
    S1674App (l := l) e U ≫ S1674App (l := l) e U =
      S1674App (l := l) (e ≫ e) U :=
  S1691App_vcomp (l := l) e U

theorem S1692App_id
    (U : LocallyDiscrete (S1674C (l := l))ᵒᵖ) :
    S1674App (l := l) (𝟙 (S1419AffineOver l)) U =
      𝟙 ((S1674F (l := l)).obj U) :=
  S1691App_id (l := l) U

theorem S1692SchemeEndo_sq :
    S1670SchemeEndo (l := l) ≫ S1670SchemeEndo (l := l) =
      𝟙 (S1419AffineOver l) :=
  S1685SchemeEndo_sq (l := l)

/-- Exact first missing ext lemma: app equality does not automatically
identify naturality/coherence 2-isomorphism data. -/
def S1692StrongTransExtMissing : Prop :=
  ∀ (T1 T2 : CategoryTheory.Pseudofunctor.StrongTrans
      (S1674F (l := l)) (S1674F (l := l))),
    T1.app = T2.app → T1 = T2

def S1692StrongTransFunctorialityMissing : Prop :=
  ∀ (e : S1419AffineOver l ⟶ S1419AffineOver l),
    CategoryTheory.Pseudofunctor.StrongTrans.vcomp
      (S1674StrongTransOfSchemeEndo (l := l) e)
      (S1674StrongTransOfSchemeEndo (l := l) e) =
      S1674StrongTransOfSchemeEndo (l := l) (e ≫ e)

def S1692StrongTransIdMissing : Prop :=
  S1674StrongTransOfSchemeEndo (l := l) (𝟙 (S1419AffineOver l)) =
    S1674IdentityHom (l := l)

def S1692StackLiftNonidentityRequired : Prop :=
  S1674StackLift (l := l) ≠ S1674IdentityHom (l := l)

abbrev S1692SquareTwoIsoRequired : Type 1 :=
  Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp
      (S1674StackLift (l := l)) (S1674StackLift (l := l)))
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))

abbrev S1692SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

abbrev S1692SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1692App_vcomp
#check S1692App_id
#check S1692SchemeEndo_sq
#check S1692StrongTransExtMissing
#check S1692StrongTransFunctorialityMissing
#check S1692StrongTransIdMissing
#check S1692StackLiftNonidentityRequired
#check S1692SquareTwoIsoRequired
#check S1692SignActionRequired
#check S1692SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1692StrongTransExtActual

end