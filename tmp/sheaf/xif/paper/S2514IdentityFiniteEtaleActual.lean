import tmp.sheaf.xif.paper.S1736CoverGaloisCategoryActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual

/-- The representable etale stack of a scheme over F. -/
abbrev S2514Y (T : SchemeOverField F) : EtaleStackPseudofunctor F :=
  schemeRepresentableEtalePseudofunctor F T

/-- Natural transformations between functors into a discrete category are subsingletons. -/
theorem S2514NatTrans_discrete_subsingleton {C : Type*} [Category C] {alpha : Type}
    (F G : C ⥤ Discrete alpha) : Subsingleton (F ⟶ G) := by
  constructor
  intro a b
  apply CategoryTheory.NatTrans.ext
  funext Z
  exact Subsingleton.elim _ _

/-- Modifications between strong transformations into a representable etale stack are subsingletons. -/
theorem S2514Modification_subsingleton_representable
    {W : EtaleStackPseudofunctor F} {S : SchemeOverField F}
    (L L' : W ⟶ S2514Y S) : Subsingleton (L ⟶ L') := by
  constructor
  intro a b
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  apply CategoryTheory.Cat.Hom₂.ext
  haveI : Subsingleton ((L.app U).toFunctor ⟶ (L'.app U).toFunctor) :=
    S2514NatTrans_discrete_subsingleton _ _
  exact Subsingleton.elim _ _

/-- The S2482 orbicurve stack is representable over S2482AffineOver. -/
theorem S2514Modification_subsingleton_stack
    {W : EtaleStackPseudofunctor F} (L L' : W ⟶ S2482Orbicurve.stack.fiber) :
    Subsingleton (L ⟶ L') :=
  S2514Modification_subsingleton_representable (S := S2482AffineOver) L L'

/-! ## 1. The identity cover is finite etale -/

/-- The structure map of the identity cover is representable by the identity
scheme morphism. -/
noncomputable def S2514IdSchemeRepresentableMap (T : SchemeOverField F) :
    SchemeRepresentableMap (𝟙 T) where
  transformation := Pseudofunctor.StrongTrans.id (S2514Y T)
  app_eq := by
    intro U
    apply Cat.ext
    apply Discrete.functor_ext
    intro P
    apply Discrete.ext
    rfl

/-- The comparison 2-isomorphism of the identity-point square:
q ≫ id ≅ id ≫ q. -/
noncomputable def S2514IdCommutes (T : SchemeOverField F)
    (q : Pseudofunctor.StrongTrans (S2514Y T) S2482Orbicurve.stack.fiber) :
    Iso (Pseudofunctor.StrongTrans.vcomp q
        (Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S2514Y T)) q) :=
  (Pseudofunctor.StrongTrans.rightUnitor q).trans
    (Pseudofunctor.StrongTrans.leftUnitor q).symm

/-- The two-pullback witness of the identity-point base-change square.  The
lift of a cone is its second leg; the two comparison isomorphisms are the right
unitors, composed with the cone's own comparison for the first leg.  The three
coherence fields are equalities of 2-cells into the representable S1726 stack,
hence subsingletons. -/
noncomputable def S2514IdWitness (T : SchemeOverField F)
    (q : Pseudofunctor.StrongTrans (S2514Y T) S2482Orbicurve.stack.fiber) :
    (EtalePseudofunctorSquare.mk (P := S2514Y T) (X := S2482Orbicurve.stack.fiber)
      (Y := S2514Y T) (Z := S2482Orbicurve.stack.fiber) q
      (Pseudofunctor.StrongTrans.id (S2514Y T))
      (Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber) q
      (S2514IdCommutes T q)).TwoPullbackWitness where
  lift W cone := cone.toY
  liftToX W cone := cone.commutes.symm.trans
    (@Bicategory.rightUnitor (EtaleStackPseudofunctor F) _ W
      S2482Orbicurve.stack.fiber cone.toX)
  liftToY W cone :=
    @Bicategory.rightUnitor (EtaleStackPseudofunctor F) _ W
      (S2514Y T) cone.toY
  liftTwoCell W source target morphism := morphism.toY
  liftTwoCell_toX := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp source.toY q) ⟶
         (Pseudofunctor.StrongTrans.vcomp target.toY q)) :=
      S2514Modification_subsingleton_stack _ _
    exact Subsingleton.elim _ _
  liftTwoCell_toY := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp source.toY
          (Pseudofunctor.StrongTrans.id (S2514Y T))) ⟶
         (Pseudofunctor.StrongTrans.vcomp target.toY
          (Pseudofunctor.StrongTrans.id (S2514Y T)))) :=
      S2514Modification_subsingleton_representable (S := T) _ _
    exact Subsingleton.elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    haveI : Subsingleton (first ⟶ second) :=
      S2514Modification_subsingleton_representable (S := T) first second
    exact Subsingleton.elim _ _

/-- The actual base-change presentation of the identity map at a scheme-valued
point. -/
noncomputable def S2514IdBaseChange (T : SchemeOverField F)
    (q : Pseudofunctor.StrongTrans (S2514Y T) S2482Orbicurve.stack.fiber) :
    EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber) T q where
  pullbackScheme := T
  projection := 𝟙 T
  projectionMap := S2514IdSchemeRepresentableMap T
  toSource := q
  commutes := S2514IdCommutes T q
  isPullback := S2514IdWitness T q

/-- The identity cover of the actual S1726 orbicurve is representably finite
etale.  The finite-etale property of the identity scheme morphism is the
standard identity instance. -/
noncomputable def S2514IdentityFiniteEtale :
    EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber) where
  baseChange T q := S2514IdBaseChange T q
  hasProperty T q := by
    change IsFinite (Over.Hom.left (𝟙 T)) ∧ Etale (Over.Hom.left (𝟙 T))
    exact ⟨inferInstance, inferInstance⟩

/-- The exact S1736 terminal input is now inhabited for the actual S1726
orbicurve. -/
theorem S2514IdentityFiniteEtaleActual :
    S1736IdentityFiniteEtale (F := F) (X := S2482Orbicurve) :=
  ⟨S2514IdentityFiniteEtale⟩

/-- The same statement in the form used by S1736's finite-limit assembly. -/
theorem S2514IdentityFiniteEtaleActual_nonempty :
    S1736IdentityFiniteEtale (F := F) (X := S2482Orbicurve) :=
  S2514IdentityFiniteEtaleActual

/-! ## 2. The terminal object and the terminal field -/

/-- The identity cover, now with its finite-etale proof. -/
noncomputable def S2514TerminalCover : OrbicurveFiniteEtaleCover S2482Orbicurve :=
  S1736TerminalCover (F := F) (X := S2482Orbicurve) S2514IdentityFiniteEtale

/-- The identity cover is terminal in the actual Category.{1,1}. -/
noncomputable def S2514TerminalCover_isTerminal :
    @IsTerminal _ (S1736ActualCategory (F := F) (X := S2482Orbicurve))
      S2514TerminalCover :=
  S1736TerminalCover_isTerminal (F := F) (X := S2482Orbicurve)
    S2514IdentityFiniteEtale

/-- The terminal field of PreGaloisCategory on the actual S1728 category. -/
theorem S2514HasTerminalActual :
    @HasTerminal (OrbicurveFiniteEtaleCover S2482Orbicurve)
      (S1736ActualCategory (F := F) (X := S2482Orbicurve)) :=
  S1736HasTerminal_of_identity_finiteEtale (F := F) (X := S2482Orbicurve)
    S2514IdentityFiniteEtale


end LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual
end
