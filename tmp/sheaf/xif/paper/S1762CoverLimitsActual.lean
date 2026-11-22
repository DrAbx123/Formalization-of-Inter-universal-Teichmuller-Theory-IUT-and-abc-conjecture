import tmp.sheaf.xif.paper.S1736CoverGaloisCategoryActual

/-!
# S1762: the terminal object of the actual S1728 cover category, and the
remaining limit/coproduct obligations

## Target

The actual category is the S1728 2-isomorphism quotient category

  Category.{1,1} (OrbicurveFiniteEtaleCover S1726Orbicurve)

of representably finite-etale stack maps to the S1726 D6 orbicurve.  S1736
recorded the five Mathlib PreGaloisCategory fields on this category and six
exact missing propositions.

## What is constructed here

* The identity cover is finite etale.  For the actual S1726 orbicurve the
  underlying stack is the representable etale stack of the affine base
  S1726AffineOver (S1726Orbicurve_stack_fiber).  Consequently, modifications
  between strong transformations into it are subsingletons, and the coherence
  fields of the identity-point base-change square are proofs.  The base-change
  presentation is constructed explicitly: pullback scheme = the test scheme,
  projection = identity, comparison = the right/left unitors, and the
  two-pullback witness has the obvious lift and comparison isomorphisms.

* Consequently the identity cover is the terminal object of the actual
  Category.{1,1}, and the terminal field of PreGaloisCategory is closed:

    S1762HasTerminalActual : HasTerminal (S1736ActualCategory ...)
    S1762HasTerminalS1728  : HasTerminal S1728ActualCategory11

* The finite-limit field now reduces to pullbacks alone
  (S1762HasFiniteLimits_of_pullbacks), and the actual PreGaloisCategory
  assembles from the four remaining exact inputs, with the terminal input
  discharged (S1762PreGaloisCategoryOfRemainingInputs).

## Precise remaining missing

No construction of pullbacks or finite coproducts in the actual cover category
is present in the tree, and none is asserted here.  The exact remaining
propositions are

  S1762PullbackObligationActual
  S1762FiniteCoproductObligationActual

namely Mathlib's literal fields HasPullbacks and HasFiniteCoproducts on the
actual S1728 category.  The geometric inputs whose absence makes these the
first missing statements are:

* pullbacks: the bicategorical fibre product of the two cover source stacks
  over the common cover, a two-pullback witness for its defining square, finite
  etaleness of the two projections, and the induced universal property in the
  2-isomorphism quotient;
* finite coproducts: the disjoint union stack of the two cover source stacks
  over the base, finite etaleness of the two inclusions, the initial object,
  and the induced coproduct universal property in the 2-isomorphism quotient.

The two-pullback witness alone does not give the quotient-category limit; that
is the quotient universal-property half which is also missing.

## Honest boundary

No sorry, no new axiom, no Shrink, no ULift, and no fake category or limit is
used.  The construction of the identity cover is a genuine inhabitant of
EtaleStackFiniteEtaleMorphism; its only nonconstructive inputs are propext,
Classical.choice and Quot.sound, inherited from the S1728 2-isomorphism
quotient.  The remaining obligations are recorded as exact propositions, not
inhabited.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual

namespace LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual

/-! ## 0. The actual orbicurve and 2-cell uniqueness into representable stacks -/

/-- The S1726 field. -/
abbrev S1762K : Type := S1726K

/-- The actual S1726 D6 orbicurve. -/
abbrev S1762X : HyperbolicOrbicurve S1762K := S1726Orbicurve

/-- The representable etale stack of a scheme over the S1726 field. -/
abbrev S1762Y (T : SchemeOverField S1762K) : EtaleStackPseudofunctor S1762K :=
  schemeRepresentableEtalePseudofunctor S1762K T

/-- Natural transformations between functors into a discrete category are
subsingletons. -/
theorem S1762NatTrans_discrete_subsingleton {C : Type*} [Category C] {alpha : Type}
    (F G : C ⥤ Discrete alpha) : Subsingleton (F ⟶ G) := by
  constructor
  intro a b
  apply CategoryTheory.NatTrans.ext
  funext Z
  exact Subsingleton.elim _ _

/-- Modifications between strong transformations into a representable etale
stack are subsingletons.  Every component lands in a discrete category. -/
theorem S1762Modification_subsingleton_representable
    {W : EtaleStackPseudofunctor S1762K} {S : SchemeOverField S1762K}
    (L L' : W ⟶ S1762Y S) : Subsingleton (L ⟶ L') := by
  constructor
  intro a b
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  apply CategoryTheory.Cat.Hom₂.ext
  haveI : Subsingleton ((L.app U).toFunctor ⟶ (L'.app U).toFunctor) :=
    S1762NatTrans_discrete_subsingleton _ _
  exact Subsingleton.elim _ _

/-- The actual S1726 orbicurve stack is the representable etale stack of the
S1726 affine base, so the same 2-cell uniqueness holds for transformations into
it.  This is the only place where the argument uses the concrete S1726
orbicurve rather than an arbitrary hyperbolic orbicurve. -/
theorem S1762Modification_subsingleton_stack
    {W : EtaleStackPseudofunctor S1762K} (L L' : W ⟶ S1762X.stack.fiber) :
    Subsingleton (L ⟶ L') :=
  S1762Modification_subsingleton_representable (S := S1726AffineOver) L L'

/-! ## 1. The identity cover is finite etale -/

/-- The structure map of the identity cover is representable by the identity
scheme morphism. -/
noncomputable def S1762IdSchemeRepresentableMap (T : SchemeOverField S1762K) :
    SchemeRepresentableMap (𝟙 T) where
  transformation := Pseudofunctor.StrongTrans.id (S1762Y T)
  app_eq := by
    intro U
    apply Cat.ext
    apply Discrete.functor_ext
    intro P
    apply Discrete.ext
    rfl

/-- The comparison 2-isomorphism of the identity-point square:
q ≫ id ≅ id ≫ q. -/
noncomputable def S1762IdCommutes (T : SchemeOverField S1762K)
    (q : Pseudofunctor.StrongTrans (S1762Y T) S1762X.stack.fiber) :
    Iso (Pseudofunctor.StrongTrans.vcomp q
        (Pseudofunctor.StrongTrans.id S1762X.stack.fiber))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S1762Y T)) q) :=
  (Pseudofunctor.StrongTrans.rightUnitor q).trans
    (Pseudofunctor.StrongTrans.leftUnitor q).symm

/-- The two-pullback witness of the identity-point base-change square.  The
lift of a cone is its second leg; the two comparison isomorphisms are the right
unitors, composed with the cone's own comparison for the first leg.  The three
coherence fields are equalities of 2-cells into the representable S1726 stack,
hence subsingletons. -/
noncomputable def S1762IdWitness (T : SchemeOverField S1762K)
    (q : Pseudofunctor.StrongTrans (S1762Y T) S1762X.stack.fiber) :
    (EtalePseudofunctorSquare.mk (P := S1762Y T) (X := S1762X.stack.fiber)
      (Y := S1762Y T) (Z := S1762X.stack.fiber) q
      (Pseudofunctor.StrongTrans.id (S1762Y T))
      (Pseudofunctor.StrongTrans.id S1762X.stack.fiber) q
      (S1762IdCommutes T q)).TwoPullbackWitness where
  lift W cone := cone.toY
  liftToX W cone := cone.commutes.symm.trans
    (@Bicategory.rightUnitor (EtaleStackPseudofunctor S1762K) _ W
      S1762X.stack.fiber cone.toX)
  liftToY W cone :=
    @Bicategory.rightUnitor (EtaleStackPseudofunctor S1762K) _ W
      (S1762Y T) cone.toY
  liftTwoCell W source target morphism := morphism.toY
  liftTwoCell_toX := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp source.toY q) ⟶
         (Pseudofunctor.StrongTrans.vcomp target.toY q)) :=
      S1762Modification_subsingleton_stack _ _
    exact Subsingleton.elim _ _
  liftTwoCell_toY := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp source.toY
          (Pseudofunctor.StrongTrans.id (S1762Y T))) ⟶
         (Pseudofunctor.StrongTrans.vcomp target.toY
          (Pseudofunctor.StrongTrans.id (S1762Y T)))) :=
      S1762Modification_subsingleton_representable (S := T) _ _
    exact Subsingleton.elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    haveI : Subsingleton (first ⟶ second) :=
      S1762Modification_subsingleton_representable (S := T) first second
    exact Subsingleton.elim _ _

/-- The actual base-change presentation of the identity map at a scheme-valued
point. -/
noncomputable def S1762IdBaseChange (T : SchemeOverField S1762K)
    (q : Pseudofunctor.StrongTrans (S1762Y T) S1762X.stack.fiber) :
    EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.id S1762X.stack.fiber) T q where
  pullbackScheme := T
  projection := 𝟙 T
  projectionMap := S1762IdSchemeRepresentableMap T
  toSource := q
  commutes := S1762IdCommutes T q
  isPullback := S1762IdWitness T q

/-- The identity cover of the actual S1726 orbicurve is representably finite
etale.  The finite-etale property of the identity scheme morphism is the
standard identity instance. -/
noncomputable def S1762IdentityFiniteEtale :
    EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id S1762X.stack.fiber) where
  baseChange T q := S1762IdBaseChange T q
  hasProperty T q := by
    change IsFinite (Over.Hom.left (𝟙 T)) ∧ Etale (Over.Hom.left (𝟙 T))
    exact ⟨inferInstance, inferInstance⟩

/-- The exact S1736 terminal input is now inhabited for the actual S1726
orbicurve. -/
theorem S1762IdentityFiniteEtaleActual :
    S1736IdentityFiniteEtale (F := S1762K) (X := S1762X) :=
  ⟨S1762IdentityFiniteEtale⟩

/-- The same statement in the form used by S1736's finite-limit assembly. -/
theorem S1762IdentityFiniteEtaleActual_nonempty :
    S1736IdentityFiniteEtale (F := S1762K) (X := S1762X) :=
  S1762IdentityFiniteEtaleActual

/-! ## 2. The terminal object and the terminal field -/

/-- The identity cover, now with its finite-etale proof. -/
noncomputable def S1762TerminalCover : OrbicurveFiniteEtaleCover S1762X :=
  S1736TerminalCover (F := S1762K) (X := S1762X) S1762IdentityFiniteEtale

/-- The identity cover is terminal in the actual Category.{1,1}. -/
noncomputable def S1762TerminalCover_isTerminal :
    @IsTerminal _ (S1736ActualCategory (F := S1762K) (X := S1762X))
      S1762TerminalCover :=
  S1736TerminalCover_isTerminal (F := S1762K) (X := S1762X)
    S1762IdentityFiniteEtale

/-- The terminal field of PreGaloisCategory on the actual S1728 category. -/
theorem S1762HasTerminalActual :
    @HasTerminal (OrbicurveFiniteEtaleCover S1762X)
      (S1736ActualCategory (F := S1762K) (X := S1762X)) :=
  S1736HasTerminal_of_identity_finiteEtale (F := S1762K) (X := S1762X)
    S1762IdentityFiniteEtale

/-- The terminal field stated directly on the S1728 paper category
S1728ActualCategory11. -/
theorem S1762HasTerminalS1728 :
    @HasTerminal S1728Cover S1728ActualCategory11 :=
  S1762HasTerminalActual

/-! ## 3. Pullbacks and coproducts: exact remaining obligations -/

/-- The exact pullback field on the actual S1728 category.  This is the first
remaining missing construction for finite limits. -/
def S1762PullbackObligationActual : Prop :=
  S1736PullbackObligation (F := S1762K) (X := S1762X)

/-- The exact finite-coproduct field on the actual S1728 category. -/
def S1762FiniteCoproductObligationActual : Prop :=
  S1736FiniteCoproductObligation (F := S1762K) (X := S1762X)

/-- The exact quotient-by-finite-groups field on the actual S1728 category. -/
def S1762FiniteGroupQuotientObligationActual : Prop :=
  S1736FiniteGroupQuotientObligation (F := S1762K) (X := S1762X)

/-- The exact mono/direct-summand field on the actual S1728 category. -/
def S1762MonoDirectSummandObligationActual : Prop :=
  S1736MonoDirectSummandObligation (F := S1762K) (X := S1762X)

/-- The exact fiber-functor obligation on the actual S1728 category. -/
def S1762FiberFunctorObligationActual
    (P : @PreGaloisCategory.{1, 1} (OrbicurveFiniteEtaleCover S1762X)
      (S1736ActualCategory (F := S1762K) (X := S1762X))) : Prop :=
  S1736ActualFiberFunctorObligation (F := S1762K) (X := S1762X) P

/-! ## 4. Finite limits with the terminal field discharged -/

/-- The finite-limit field now depends only on the pullback obligation. -/
theorem S1762HasFiniteLimits_of_pullbacks
    (hPull : S1762PullbackObligationActual) :
    S1736ObligationFiniteLimits (F := S1762K) (X := S1762X) :=
  S1736HasFiniteLimits_of_inputs (F := S1762K) (X := S1762X)
    S1762IdentityFiniteEtaleActual_nonempty hPull

/-! ## 5. Conditional assembly of the actual PreGaloisCategory -/

/-- The actual PreGaloisCategory assembles from the four remaining exact
inputs.  The terminal input is no longer an input: it is constructed above. -/
theorem S1762PreGaloisCategoryOfRemainingInputs
    (hPull : S1762PullbackObligationActual)
    (hCoprod : S1762FiniteCoproductObligationActual)
    (hQuot : S1762FiniteGroupQuotientObligationActual)
    (hMono : S1762MonoDirectSummandObligationActual) :
    S1736ActualPreGaloisObligation (F := S1762K) (X := S1762X) :=
  S1736PreGaloisCategoryOfInputs (F := S1762K) (X := S1762X)
    S1762IdentityFiniteEtaleActual_nonempty hPull hCoprod hQuot hMono

/-- The exact PreGaloisCategory obligation, limited to the actual S1726
orbicurve, is equivalent to the four remaining fields. -/
theorem S1762ActualPreGalois_iff_remaining :
    S1736ActualPreGaloisObligation (F := S1762K) (X := S1762X) ↔
      S1736ActualFieldObligation (F := S1762K) (X := S1762X) :=
  S1736ActualPreGalois_iff_fields (F := S1762K) (X := S1762X)

/-! ## 6. Exact first missing report -/

/-- The first missing construction for pullbacks: the literal HasPullbacks
field of the actual S1728 category.  Its geometric content is the bicategorical
fibre product of the cover source stacks together with finite etaleness of the
two projections and the quotient universal property; see the module docstring. -/
def S1762FirstMissingPullback : Prop :=
  S1762PullbackObligationActual

/-- The first missing construction for finite coproducts: the literal
HasFiniteCoproducts field of the actual S1728 category.  Its geometric content
is the disjoint union of the cover source stacks (including the initial
object), finite etaleness of the two inclusions, and the quotient coproduct
universal property. -/
def S1762FirstMissingFiniteCoproduct : Prop :=
  S1762FiniteCoproductObligationActual

/-- The remaining quotient and mono obligations, listed explicitly so that the
exact first missing statement is complete. -/
def S1762FirstMissingQuotients : Prop :=
  S1762FiniteGroupQuotientObligationActual

def S1762FirstMissingMono : Prop :=
  S1762MonoDirectSummandObligationActual

/-! ## 7. Axiom audit and checks -/

#check S1762IdentityFiniteEtale
#check S1762IdentityFiniteEtaleActual
#check S1762TerminalCover
#check S1762TerminalCover_isTerminal
#check S1762HasTerminalActual
#check S1762HasTerminalS1728
#check S1762PullbackObligationActual
#check S1762FiniteCoproductObligationActual
#check S1762HasFiniteLimits_of_pullbacks
#check S1762PreGaloisCategoryOfRemainingInputs
#check S1762FirstMissingPullback
#check S1762FirstMissingFiniteCoproduct
#check S1762FirstMissingQuotients
#check S1762FirstMissingMono

#print axioms S1762Modification_subsingleton_stack
#print axioms S1762IdentityFiniteEtale
#print axioms S1762IdentityFiniteEtaleActual
#print axioms S1762TerminalCover_isTerminal
#print axioms S1762HasTerminalActual
#print axioms S1762HasTerminalS1728
#print axioms S1762HasFiniteLimits_of_pullbacks
#print axioms S1762PreGaloisCategoryOfRemainingInputs

end LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
