import tmp.sheaf.xif.paper.S1670OrbicurveStackLiftActual

-- S1674: actual StrongTrans stack lift of S1670SchemeEndo via the
-- representable discrete pseudofunctor.  Square/nontriviality/signAction/
-- quotient remain exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1674StackStrongTransActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1670OrbicurveStackLiftActual

variable {l : PrimeGeFive}

abbrev S1674C : Type 1 := Iut.SchemeOverField (S1348K l)

abbrev S1674F : Iut.EtaleStackPseudofunctor (S1348K l) :=
  Iut.schemeRepresentableEtalePseudofunctor (S1348K l) (S1419AffineOver l)

/-- App component of the representable StrongTrans induced by a scheme
endomorphism: postcompose every section with g. -/
noncomputable def S1674App
    (g : S1419AffineOver l ⟶ S1419AffineOver l)
    (U : LocallyDiscrete (S1674C (l := l))ᵒᵖ) :
    (S1674F (l := l)).obj U ⟶ (S1674F (l := l)).obj U :=
  (Discrete.functor
    (fun P : Opposite.unop U.as ⟶ S1419AffineOver l =>
      Discrete.mk (P ≫ g))).toCatHom

/-- Actual StrongTrans from the representable scheme endomorphism. -/
noncomputable def S1674StrongTransOfSchemeEndo
    (g : S1419AffineOver l ⟶ S1419AffineOver l) :
    CategoryTheory.Pseudofunctor.StrongTrans
      (S1674F (l := l)) (S1674F (l := l)) where
  app U := S1674App (l := l) g U
  naturality f := by
    apply eqToIso
    apply CategoryTheory.Cat.ext
    apply CategoryTheory.Functor.ext
    · intro X Y h
      apply ULift.ext
      exact Subsingleton.elim _ _
    · intro X
      rfl
  naturality_naturality := by
    intro a b f g_1 eta
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g_1
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _

/-- Actual stack lift of the S1670 scheme endomorphism. -/
noncomputable def S1674StackLift :
    (S1536XF (l := l)).Hom (S1536XF (l := l)) :=
  S1674StrongTransOfSchemeEndo (l := l) (S1670SchemeEndo (l := l))

noncomputable def S1674IdentityHom :
    (S1536XF (l := l)).Hom (S1536XF (l := l)) :=
  Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l))

/-- Exact missing: nonidentity of the actual stack lift. -/
def S1674StackLiftNonidentityRequired : Prop :=
  S1674StackLift (l := l) ≠ S1674IdentityHom (l := l)

/-- Exact missing: square TwoIso to the identity. -/
abbrev S1674SquareTwoIsoRequired : Type 1 :=
  Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp
      (S1674StackLift (l := l)) (S1674StackLift (l := l)))
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))

abbrev S1674SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

abbrev S1674SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1674App
#check S1674StrongTransOfSchemeEndo
#check S1674StackLift
#check S1674IdentityHom
#check S1674StackLiftNonidentityRequired
#check S1674SquareTwoIsoRequired
#check S1674SignActionRequired
#check S1674SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1674StackStrongTransActual

end