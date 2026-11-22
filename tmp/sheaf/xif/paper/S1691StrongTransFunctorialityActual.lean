import tmp.sheaf.xif.paper.S1685StackTwoIsoActual

-- S1691: app-level functoriality of S1674StrongTransOfSchemeEndo is actual;
-- full StrongTrans equality, TwoIso, nonidentity, signAction/quotient missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1691StrongTransFunctorialityActual

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

variable {l : PrimeGeFive}

/-- Actual app-level functoriality: composing the representable app twice is
the app of the composite scheme endomorphism. -/
theorem S1691App_vcomp
    (e : S1419AffineOver l ⟶ S1419AffineOver l)
    (U : LocallyDiscrete (S1674C (l := l))ᵒᵖ) :
    S1674App (l := l) e U ≫ S1674App (l := l) e U =
      S1674App (l := l) (e ≫ e) U := by
  apply CategoryTheory.Cat.ext
  apply CategoryTheory.Functor.ext
  · intro Y f f_1
    apply ULift.ext
    exact Subsingleton.elim _ _
  · intro X
    apply Discrete.ext
    simp [S1674App, Category.assoc]

/-- Actual app-level identity: the app of the identity scheme endomorphism is
the identity functor. -/
theorem S1691App_id
    (U : LocallyDiscrete (S1674C (l := l))ᵒᵖ) :
    S1674App (l := l) (𝟙 (S1419AffineOver l)) U =
      𝟙 ((S1674F (l := l)).obj U) := by
  apply CategoryTheory.Cat.ext
  apply CategoryTheory.Functor.ext
  · intro Y f f_1
    apply ULift.ext
    exact Subsingleton.elim _ _
  · intro X
    apply Discrete.ext
    simp [S1674App]

theorem S1691SchemeEndo_sq :
    S1670SchemeEndo (l := l) ≫ S1670SchemeEndo (l := l) =
      𝟙 (S1419AffineOver l) :=
  S1685SchemeEndo_sq (l := l)

/-- Exact missing: full StrongTrans functoriality for the composite. -/
def S1691StrongTransFunctorialityMissing : Prop :=
  ∀ (e : S1419AffineOver l ⟶ S1419AffineOver l),
    CategoryTheory.Pseudofunctor.StrongTrans.vcomp
      (S1674StrongTransOfSchemeEndo (l := l) e)
      (S1674StrongTransOfSchemeEndo (l := l) e) =
      S1674StrongTransOfSchemeEndo (l := l) (e ≫ e)

/-- Exact missing: full StrongTrans identity compatibility. -/
def S1691StrongTransIdMissing : Prop :=
  S1674StrongTransOfSchemeEndo (l := l) (𝟙 (S1419AffineOver l)) =
    S1674IdentityHom (l := l)

def S1691StackLiftNonidentityRequired : Prop :=
  S1674StackLift (l := l) ≠ S1674IdentityHom (l := l)

abbrev S1691SquareTwoIsoRequired : Type 1 :=
  Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp
      (S1674StackLift (l := l)) (S1674StackLift (l := l)))
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))

abbrev S1691SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

abbrev S1691SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1691App_vcomp
#check S1691App_id
#check S1691SchemeEndo_sq
#check S1691StrongTransFunctorialityMissing
#check S1691StrongTransIdMissing
#check S1691StackLiftNonidentityRequired
#check S1691SquareTwoIsoRequired
#check S1691SignActionRequired
#check S1691SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1691StrongTransFunctorialityActual

end