/-
# S2512: the affine chart of the projective line over UB is representably an
open immersion of etale stacks

For the chart map of the projective line P1_UB = Proj UB[X0,X1] over the unified
base UB = Q(i),

    S2508ChartOverMap : Spec UB[x] --> P1_UB ,

which is an open immersion of schemes (S2508ChartMap_isOpenImmersion), the induced
strong transformation of representable etale stacks is

    S2508StackOpenMap = S1742StrongTransOfHom S2508ChartOverMap .

This file constructs

    S2512StackOpenImmersion : Iut.EtaleStackOpenImmersion S2508StackOpenMap ,

i.e. the third field of the cusp datum of S2508.

## The construction

This is the 2-categorical form of "the Yoneda image of an open immersion of
schemes is representably an open immersion".  For a test scheme T and a
scheme-valued point point : h_T --> h_B of the target stack, the 2-Yoneda
comparison of S1742 (S1742HomOfStrongTrans) turns point into an actual morphism
g : T --> B of schemes over UB.  The base change of the open immersion f : A --> B
along g is the schematic fibre product

    P := T x_B A,   pX : P --> A,   pY : P --> T ,

displayed by

    P --pX--> A
    |          |
    pY         f
    v          v
    T --g---> B

The two projections are morphisms of UB-schemes by the pullback condition and the
structure-map triangles of f and g.  The square of representable etale stacks
induced by this scheme pullback square is a bicategorical pullback.  This is the
representable two-pullback theorem of the tree (S1911Witness in
S1911RepresentableTwoPullbackActual); the proof is reproduced here as the
S2512G series in the generality of an arbitrary base field, so that it applies
at UB.  Its lift is built pointwise by IsPullback.lift, and all comparison
2-cells exist because 2-cells into a representable stack are subsingletons.

Finally pY is an open immersion, being the base change of the open immersion f
(Mathlib: IsOpenImmersion is stable under base change).  This yields the
base-change presentation at every scheme-valued point, i.e. the representable
open immersion of the stack map.

## Honest boundary

No sorry, no new axiom, no Shrink/ULift/PUnit, no fake 2-cell.  The only inputs
are the actual scheme fibre product and the 2-Yoneda comparison; the abstract
2-categorical work is the general-field form of S1911 (S1926 instantiates it at
the field of S1726, which is not UB).

The remaining two fields of S2508CuspDatum are NOT constructed here: the boundary
point at infinity of P1_UB and its separation from the affine chart remain the
exact missing scheme-level inputs (S2508).  From this file, the nonemptiness of
the cusp datum reduces from three fields to those two (S2512Missing_iff).
-/

import tmp.sheaf.xif.paper.S2508CuspDataUB
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.MorphismProperty.Limits

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2505AwayEquivActual
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

namespace LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB

/-! ## 1. 2-cells into a representable stack are subsingletons -/

/-- Natural transformations between functors into a discrete category are
subsingletons. -/
theorem S2512NatTrans_discrete_subsingleton {D : Type*} [Category D] {alpha : Type}
    (L1 L2 : D ⥤ Discrete alpha) : Subsingleton (L1 ⟶ L2) := by
  constructor
  intro a b
  apply CategoryTheory.NatTrans.ext
  funext Z
  exact Subsingleton.elim _ _

/-! ## 2. Values of a strong transformation into a representable stack

These are the general-field forms of S1911's sections 2-5 and of S1926's
sections 1-3, with the fixed field of S1726 replaced by an arbitrary field F. -/

section Generic

variable {F : Type} [Field F]

/-- The representable category-valued etale pseudofunctor of a scheme over F. -/
abbrev S2512YS (S : Iut.SchemeOverField F) : Iut.EtaleStackPseudofunctor F :=
  Iut.schemeRepresentableEtalePseudofunctor F S

section Values

variable {W : Iut.EtaleStackPseudofunctor F} {T : Iut.SchemeOverField F}

/-- The value of a strong transformation into a representable etale stack, at a
test object and an object of the source fibre: the underlying morphism of
schemes. -/
noncomputable def S2512Val (L : Pseudofunctor.StrongTrans W (S2512YS T))
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    U.as.unop ⟶ T :=
  ((L.app U).toFunctor.obj a).as

/-- The defining computation rule of S2512Val. -/
@[simp] theorem S2512Val_def (L : Pseudofunctor.StrongTrans W (S2512YS T))
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S2512Val L U a = ((L.app U).toFunctor.obj a).as := rfl

/-- The component of a vertical composite is the composite of the components. -/
theorem S2512App_vcomp {X Z : Iut.SchemeOverField F}
    (L : Pseudofunctor.StrongTrans W (S2512YS X))
    (M : Pseudofunctor.StrongTrans (S2512YS X) (S2512YS Z))
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp L M).app U = L.app U ≫ M.app U := rfl

/-- The value of the 2-Yoneda strong transformation of a scheme morphism. -/
theorem S2512Val_strongTransOfHom {S U : Iut.SchemeOverField F} (h : S ⟶ U)
    (a' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (a : (S2512YS S).obj a') :
    S2512Val (S1742StrongTransOfHom h) a' a = a.as ≫ h := by
  rw [S2512Val_def]
  change ((S1742App h a').toFunctor.obj a).as = a.as ≫ h
  rw [← Discrete.mk_as a, S1742App_obj]

/-- Composition with a strong transformation of representable stacks acts on
values by composition of scheme morphisms. -/
theorem S2512Val_vcomp {X Z : Iut.SchemeOverField F}
    (L : Pseudofunctor.StrongTrans W (S2512YS X))
    (M : Pseudofunctor.StrongTrans (S2512YS X) (S2512YS Z))
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S2512Val (Pseudofunctor.StrongTrans.vcomp L M) U a =
      S2512Val L U a ≫ S1742HomOfStrongTrans M := by
  rw [S2512Val_def, S2512Val_def, S2512App_vcomp, S1742Comp_toFunctor_obj,
    ← S1742AppEq M U, ← Discrete.mk_as ((L.app U).toFunctor.obj a),
    S1742App_obj (F := F) (S1742HomOfStrongTrans M) U]

/-- The value of a strong transformation into a representable stack is natural. -/
theorem S2512Val_naturality (L : Pseudofunctor.StrongTrans W (S2512YS T))
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (phi : a ⟶ b) (x : W.obj a) :
    S2512Val L b ((W.map phi).toFunctor.obj x) = phi.as.unop ≫ S2512Val L a x := by
  rw [S2512Val_def, S2512Val_def]
  have h := Discrete.eq_of_hom ((L.naturality phi).hom.toNatTrans.app x)
  rw [S1742Comp_toFunctor_obj, S1742Comp_toFunctor_obj, S1742YS_map (F := F) T phi,
    ← Discrete.mk_as ((L.app a).toFunctor.obj x), S1742Fiber_map_obj] at h
  exact h

end Values

/-- Modifications between strong transformations into a representable etale
stack are subsingletons.  Every component lands in a discrete category. -/
theorem S2512Modification_subsingleton {W : Iut.EtaleStackPseudofunctor F}
    {T : Iut.SchemeOverField F}
    (L L' : Pseudofunctor.StrongTrans W (S2512YS T)) :
    Subsingleton (L ⟶ L') := by
  constructor
  intro a b
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  apply CategoryTheory.Cat.Hom₂.ext
  haveI : Subsingleton ((L.app U).toFunctor ⟶ (L'.app U).toFunctor) :=
    S2512NatTrans_discrete_subsingleton _ _
  exact Subsingleton.elim _ _

/-- Two strong transformations into a representable stack with equal values are
2-isomorphic.  This is the form in which every comparison 2-cell of the lift is
built. -/
theorem S2512Val_isoOfValEq {W : Iut.EtaleStackPseudofunctor F}
    {T : Iut.SchemeOverField F}
    {L L' : Pseudofunctor.StrongTrans W (S2512YS T)}
    (h : forall (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U),
      S2512Val L U a = S2512Val L' U a) :
    Nonempty (Iso L L') := by
  refine ⟨Pseudofunctor.StrongTrans.isoMk (fun U => eqToIso (by
    apply Cat.ext
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro a
      apply Discrete.ext
      exact h U a
    case h_map =>
      intro X Y f
      apply ULift.ext
      exact Subsingleton.elim _ _)) ?_⟩
  intro a b f
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-! ## 3. The cone condition -/

section ConeCondition

variable {X Y Z P : Iut.SchemeOverField F}

/-- The underlying scheme morphism of the first base leg of a square of
representable stacks. -/
noncomputable def S2512BaseF
    (sq : EtalePseudofunctorSquare (S2512YS P) (S2512YS X) (S2512YS Y) (S2512YS Z)) :
    X ⟶ Z :=
  S1742HomOfStrongTrans sq.xToBase

/-- The underlying scheme morphism of the second base leg of a square of
representable stacks. -/
noncomputable def S2512BaseG
    (sq : EtalePseudofunctorSquare (S2512YS P) (S2512YS X) (S2512YS Y) (S2512YS Z)) :
    Y ⟶ Z :=
  S1742HomOfStrongTrans sq.yToBase

/-- The cone condition.  For a cone over the square, the two composites of the
cone's legs with the square's base legs agree on underlying scheme morphisms. -/
theorem S2512ConeCondition
    {sq : EtalePseudofunctorSquare (S2512YS P) (S2512YS X) (S2512YS Y) (S2512YS Z)}
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S2512Val c.toX U a ≫ S2512BaseF sq = S2512Val c.toY U a ≫ S2512BaseG sq := by
  have h := Discrete.eq_of_hom ((c.commutes.hom.as.app U).toNatTrans.app a)
  simpa only [S2512BaseF, S2512BaseG, ← S2512Val_def, S2512Val_vcomp] using h

end ConeCondition

/-! ## 4. The lift of a cone, pointwise by pullback.lift -/

section Lift

variable {X Y Z P : Iut.SchemeOverField F} {pX : P ⟶ X} {pY : P ⟶ Y}
variable {sq : EtalePseudofunctorSquare (S2512YS P) (S2512YS X) (S2512YS Y) (S2512YS Z)}

/-- The cone condition, on underlying scheme morphisms. -/
theorem S2512ConeCondition_left
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    (S2512Val c.toX U a).left ≫ (S2512BaseF sq).left =
      (S2512Val c.toY U a).left ≫ (S2512BaseG sq).left :=
  congrArg Over.Hom.left (S2512ConeCondition c U a)
/-- The underlying scheme morphism of the pullback lift of a cone. -/
noncomputable def S2512LiftSchemeVal
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    U.as.unop.left ⟶ P.left :=
  hpb.lift (S2512Val c.toX U a).left (S2512Val c.toY U a).left
    (S2512ConeCondition_left c U a)

/-- It projects to the first leg of the cone. -/
theorem S2512LiftSchemeVal_fst
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S2512LiftSchemeVal hpb c U a ≫ pX.left = (S2512Val c.toX U a).left :=
  IsPullback.lift_fst hpb _ _ _

/-- It projects to the second leg of the cone. -/
theorem S2512LiftSchemeVal_snd
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S2512LiftSchemeVal hpb c U a ≫ pY.left = (S2512Val c.toY U a).left :=
  IsPullback.lift_snd hpb _ _ _

/-- The pullback lift of a cone, as a morphism of schemes over the base. -/
noncomputable def S2512LiftVal
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) : U.as.unop ⟶ P :=
  Over.homMk (S2512LiftSchemeVal hpb c U a) (by
    rw [← pX.w, ← Category.assoc, S2512LiftSchemeVal_fst, (S2512Val c.toX U a).w])

/-- The lift projects to the first leg of the cone. -/
theorem S2512LiftVal_fst
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S2512LiftVal hpb c U a ≫ pX = S2512Val c.toX U a := by
  apply Over.OverMorphism.ext
  show S2512LiftSchemeVal hpb c U a ≫ pX.left = (S2512Val c.toX U a).left
  exact S2512LiftSchemeVal_fst hpb c U a

/-- The lift projects to the second leg of the cone. -/
theorem S2512LiftVal_snd
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S2512LiftVal hpb c U a ≫ pY = S2512Val c.toY U a := by
  apply Over.OverMorphism.ext
  show S2512LiftSchemeVal hpb c U a ≫ pY.left = (S2512Val c.toY U a).left
  exact S2512LiftSchemeVal_snd hpb c U a

/-- The first projection of the lift, on underlying scheme morphisms. -/
theorem S2512LiftVal_fst_left
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    Over.Hom.left (S2512LiftVal hpb c U a) ≫ pX.left = (S2512Val c.toX U a).left :=
  S2512LiftSchemeVal_fst hpb c U a

/-- The second projection of the lift, on underlying scheme morphisms. -/
theorem S2512LiftVal_snd_left
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    Over.Hom.left (S2512LiftVal hpb c U a) ≫ pY.left = (S2512Val c.toY U a).left :=
  S2512LiftSchemeVal_snd hpb c U a

/-- The lift is well defined on the objects of the source fibre: two objects
joined by a morphism have the same lift, because the two legs of the cone are
functors into discrete categories, and the pullback is a limit. -/
theorem S2512LiftVal_eq_of_hom
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    {a b : W.obj U} (m : a ⟶ b) :
    S2512LiftVal hpb c U a = S2512LiftVal hpb c U b := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2512LiftVal hpb c U a) = Over.Hom.left (S2512LiftVal hpb c U b)
  apply IsPullback.hom_ext hpb
  · rw [S2512LiftVal_fst_left, S2512LiftVal_fst_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((c.toX.app U).toFunctor.map m))
  · rw [S2512LiftVal_snd_left, S2512LiftVal_snd_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((c.toY.app U).toFunctor.map m))

/-- The component functor of the lift at a test object. -/
noncomputable def S2512LiftFun
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (W.obj U) ⥤ Discrete (U.as.unop ⟶ P) where
  obj a := Discrete.mk (S2512LiftVal hpb c U a)
  map m := Discrete.eqToHom (S2512LiftVal_eq_of_hom hpb c U m)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The value of the component functor. -/
theorem S2512LiftFun_obj
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    (S2512LiftFun hpb c U).obj a = Discrete.mk (S2512LiftVal hpb c U a) := rfl

/-- Naturality of the lift, on values. -/
theorem S2512LiftVal_naturality
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (phi : a ⟶ b) (x : W.obj a) :
    S2512LiftVal hpb c b ((W.map phi).toFunctor.obj x) =
      phi.as.unop ≫ S2512LiftVal hpb c a x := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2512LiftVal hpb c b ((W.map phi).toFunctor.obj x)) =
    Over.Hom.left (phi.as.unop ≫ S2512LiftVal hpb c a x)
  apply IsPullback.hom_ext hpb
  · simp only [Over.comp_left, Category.assoc, S2512LiftVal_fst_left]
    exact congrArg Over.Hom.left (S2512Val_naturality c.toX phi x)
  · simp only [Over.comp_left, Category.assoc, S2512LiftVal_snd_left]
    exact congrArg Over.Hom.left (S2512Val_naturality c.toY phi x)

/-- The lift of a cone as a strong transformation into the representable stack of
the apex. -/
noncomputable def S2512Lift
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    (W : Iut.EtaleStackPseudofunctor F) (c : sq.Cone W) :
    Pseudofunctor.StrongTrans W (S2512YS P) where
  app U := (S2512LiftFun hpb c U).toCatHom
  naturality {a b} phi := eqToIso (by
    apply Cat.ext
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro x
      show Discrete.mk (S2512LiftVal hpb c b ((W.map phi).toFunctor.obj x)) =
        ((S2512YS P).map phi).toFunctor.obj (Discrete.mk (S2512LiftVal hpb c a x))
      rw [S1742YS_map (F := F) P phi, S1742Fiber_map_obj]
      apply Discrete.ext
      show S2512LiftVal hpb c b ((W.map phi).toFunctor.obj x) =
        phi.as.unop ≫ S2512LiftVal hpb c a x
      exact S2512LiftVal_naturality hpb c phi x
    case h_map =>
      intro X Y f
      apply ULift.ext
      exact Subsingleton.elim _ _)
  naturality_naturality := by
    intro a b f g eta
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
    intro a b c f g
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _

/-- The lift compared with the first projection of the square. -/
noncomputable def S2512LiftToX
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    (W : Iut.EtaleStackPseudofunctor F) (c : sq.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2512Lift hpb W c)
      (S1742StrongTransOfHom pX)) c.toX :=
  (S2512Val_isoOfValEq (fun U a => by
    rw [S2512Val_vcomp, S1742HomOfStrongTrans_strongTransOfHom]
    exact S2512LiftVal_fst hpb c U a)).some

/-- The lift compared with the second projection of the square. -/
noncomputable def S2512LiftToY
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    (W : Iut.EtaleStackPseudofunctor F) (c : sq.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2512Lift hpb W c)
      (S1742StrongTransOfHom pY)) c.toY :=
  (S2512Val_isoOfValEq (fun U a => by
    rw [S2512Val_vcomp, S1742HomOfStrongTrans_strongTransOfHom]
    exact S2512LiftVal_snd hpb c U a)).some

/-- A morphism of cones induces the same lift, on values. -/
theorem S2512LiftVal_congr
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} {source target : sq.Cone W}
    (m : sq.ConeMorphism source target)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S2512LiftVal hpb source U a = S2512LiftVal hpb target U a := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2512LiftVal hpb source U a) =
    Over.Hom.left (S2512LiftVal hpb target U a)
  apply IsPullback.hom_ext hpb
  · rw [S2512LiftVal_fst_left, S2512LiftVal_fst_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((m.toX.as.app U).toNatTrans.app a))
  · rw [S2512LiftVal_snd_left, S2512LiftVal_snd_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((m.toY.as.app U).toNatTrans.app a))

/-- The action of the lift on morphisms of cones. -/
noncomputable def S2512LiftIso
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    {W : Iut.EtaleStackPseudofunctor F} {source target : sq.Cone W}
    (m : sq.ConeMorphism source target) :
    Iso (S2512Lift hpb W source) (S2512Lift hpb W target) :=
  (S2512Val_isoOfValEq (L := S2512Lift hpb W source) (L' := S2512Lift hpb W target)
    (fun U a => by
      show S2512LiftVal hpb source U a = S2512LiftVal hpb target U a
      exact S2512LiftVal_congr hpb m U a)).some

/-- The square is a bicategorical pullback.  The lift is the pointwise pullback
lift; the comparison 2-cells are subsingleton eliminations; the action on cone
morphisms and 2-cell extensionality exist because 2-cells into a representable
stack are subsingletons. -/
noncomputable def S2512Witness
    (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
    (hX : sq.toX = S1742StrongTransOfHom pX)
    (hY : sq.toY = S1742StrongTransOfHom pY) : sq.TwoPullbackWitness where
  lift W c := S2512Lift hpb W c
  liftToX W c := by
    rw [hX]
    exact S2512LiftToX hpb W c
  liftToY W c := by
    rw [hY]
    exact S2512LiftToY hpb W c
  liftTwoCell W source target m := (S2512LiftIso hpb m).hom
  liftTwoCell_toX := by
    intro W source target m
    exact (S2512Modification_subsingleton _ _).elim _ _
  liftTwoCell_toY := by
    intro W source target m
    exact (S2512Modification_subsingleton _ _).elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    exact (S2512Modification_subsingleton first second).elim alpha beta

end Lift

end Generic
/-! ## 5. The scheme fibre product of the chart along a scheme-valued point -/

section Application

local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

variable (T : Iut.SchemeOverField UB)
variable (point : Pseudofunctor.StrongTrans
  (Iut.schemeRepresentableEtalePseudofunctor UB T) S2508Compactification.fiber)

/-- The scheme morphism underlying a scheme-valued point of the compactification
stack of S2508, via the 2-Yoneda comparison of S1742. -/
noncomputable def S2512PointHom : T ⟶ S2508FOver :=
  S1742HomOfStrongTrans point

/-- The actual scheme fibre product of the affine chart along the point. -/
noncomputable abbrev S2512PullbackScheme : Iut.SchemeOverField UB :=
  Over.mk (pullback.fst S2508ChartOverMap.left (S2512PointHom T point).left
    ≫ S2508AffineOver.hom)

/-- The projection of the fibre product to the affine chart. -/
noncomputable def S2512ToSource : S2512PullbackScheme T point ⟶ S2508AffineOver :=
  Over.homMk (pullback.fst S2508ChartOverMap.left (S2512PointHom T point).left)
    (by rfl)

/-- The projection of the fibre product to the test scheme. -/
noncomputable def S2512Projection : S2512PullbackScheme T point ⟶ T :=
  Over.homMk (pullback.snd S2508ChartOverMap.left (S2512PointHom T point).left) (by
    show pullback.snd S2508ChartOverMap.left (S2512PointHom T point).left ≫ T.hom =
      pullback.fst S2508ChartOverMap.left (S2512PointHom T point).left
        ≫ S2508AffineOver.hom
    rw [← (S2512PointHom T point).w, ← S2508ChartOverMap.w]
    rw [← Category.assoc, ← Category.assoc]
    rw [← pullback.condition])

/-- The scheme pullback square underlying the square of representable stacks. -/
theorem S2512IsPullback :
    IsPullback (S2512ToSource T point).left (S2512Projection T point).left
      S2508ChartOverMap.left (S2512PointHom T point).left :=
  IsPullback.of_hasPullback S2508ChartOverMap.left (S2512PointHom T point).left

/-- The square commutes on underlying scheme morphisms. -/
theorem S2512SquareCommutesHom :
    S2512ToSource T point ≫ S2508ChartOverMap =
      S2512Projection T point ≫ S2512PointHom T point := by
  apply Over.OverMorphism.ext
  show pullback.fst S2508ChartOverMap.left (S2512PointHom T point).left
      ≫ S2508ChartOverMap.left =
    pullback.snd S2508ChartOverMap.left (S2512PointHom T point).left
      ≫ (S2512PointHom T point).left
  exact pullback.condition

/-- Pointwise commutation of the square of represented stacks. -/
theorem S2512CommutesVal
    (U : LocallyDiscrete (Iut.SchemeOverField UB)ᵒᵖ)
    (a : (S2512YS (F := UB) (S2512PullbackScheme T point)).obj U) :
    S2512Val (F := UB) (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S2512ToSource T point))
        (S1742StrongTransOfHom S2508ChartOverMap)) U a =
      S2512Val (F := UB) (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S2512Projection T point)) point) U a := by
  rw [S2512Val_vcomp, S2512Val_vcomp]
  rw [S2512Val_strongTransOfHom, S2512Val_strongTransOfHom]
  rw [S1742HomOfStrongTrans_strongTransOfHom]
  calc
    (a.as ≫ S2512ToSource T point) ≫ S2508ChartOverMap
        = a.as ≫ (S2512ToSource T point ≫ S2508ChartOverMap) := by
          rw [Category.assoc]
    _ = a.as ≫ (S2512Projection T point ≫ S2512PointHom T point) := by
          rw [S2512SquareCommutesHom]
    _ = (a.as ≫ S2512Projection T point) ≫ S2512PointHom T point := by
          rw [Category.assoc]

/-- The square of represented etale stacks induced by the scheme fibre product. -/
noncomputable def S2512Square :
    EtalePseudofunctorSquare (S2512YS (F := UB) (S2512PullbackScheme T point))
      (S2512YS (F := UB) S2508AffineOver) (S2512YS (F := UB) T)
      (S2512YS (F := UB) S2508FOver) where
  toX := S1742StrongTransOfHom (S2512ToSource T point)
  toY := S1742StrongTransOfHom (S2512Projection T point)
  xToBase := S1742StrongTransOfHom S2508ChartOverMap
  yToBase := point
  commutes := (S2512Val_isoOfValEq
    (L := Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S2512ToSource T point))
      (S1742StrongTransOfHom S2508ChartOverMap))
    (L' := Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S2512Projection T point)) point)
    (S2512CommutesVal T point)).some

/-- The square is a bicategorical pullback: the general-field form of the
representable two-pullback theorem of S1911. -/
noncomputable def S2512TwoPullbackWitness :
    (S2512Square T point).TwoPullbackWitness := by
  let sq := S2512Square T point
  have hF : S2512BaseF sq = S2508ChartOverMap := by
    change S1742HomOfStrongTrans sq.xToBase = S2508ChartOverMap
    rw [show sq.xToBase = S1742StrongTransOfHom S2508ChartOverMap from rfl,
      S1742HomOfStrongTrans_strongTransOfHom]
  have hG : S2512BaseG sq = S2512PointHom T point := rfl
  have hpb : IsPullback (S2512ToSource T point).left (S2512Projection T point).left
      (S2512BaseF sq).left (S2512BaseG sq).left := by
    rw [hF, hG]
    exact S2512IsPullback T point
  exact S2512Witness (P := S2512PullbackScheme T point)
    (pX := S2512ToSource T point) (pY := S2512Projection T point)
    (sq := sq) hpb rfl rfl

/-! ## 6. The base-change presentation and the representable open immersion -/

/-- The actual base-change presentation of the chart map of stacks at a
scheme-valued point, with apex the schematic fibre product. -/
noncomputable def S2512BaseChange :
    EtaleStackBaseChangePresentation (F := UB)
      (source := S2495cK.stack) (target := S2508Compactification)
      S2508StackOpenMap T point where
  pullbackScheme := S2512PullbackScheme T point
  projection := S2512Projection T point
  projectionMap :=
    { transformation := S1742StrongTransOfHom (S2512Projection T point)
      app_eq := fun U => rfl }
  toSource := S1742StrongTransOfHom (S2512ToSource T point)
  commutes := (S2512Square T point).commutes
  isPullback := S2512TwoPullbackWitness T point

/-- The projection is an open immersion: it is the base change of the open
immersion of the affine chart inside the projective line. -/
theorem S2512Projection_isOpenImmersion :
    IsOpenImmersion (S2512Projection T point).left :=
  MorphismProperty.of_isPullback (S2512IsPullback T point)
    S2508ChartOverMap_isOpenImmersion

end Application

/-- **The chart map of the projective line over the unified base UB is
representably an open immersion of etale stacks.**  This is the third field of
the cusp datum of S2508. -/
noncomputable def S2512StackOpenImmersion :
    Iut.EtaleStackOpenImmersion S2508StackOpenMap where
  baseChange T point := S2512BaseChange T point
  hasProperty T point := S2512Projection_isOpenImmersion T point

/-! ## 7. The cusp datum of S2508 with the open-immersion field supplied -/

/-- The cusp datum of S2508 from its two remaining scheme-level inputs: the
boundary point at infinity and its separation from the affine chart. -/
noncomputable def S2512CuspDatumOf (point : S2508ResidueScheme ⟶ S2508FOver)
    (separation : forall s : S2508ResidueScheme ⟶ S2508AffineOver,
      s ≫ S2508ChartOverMap ≠ point) :
    S2508CuspDatum where
  point := point
  separation := separation
  stackOpenImmersion := S2512StackOpenImmersion

/-- The exact remaining input of S2508: the point at infinity of P1_UB and its
separation from the affine chart. -/
def S2512RemainingInput : Prop :=
  exists point : S2508ResidueScheme ⟶ S2508FOver,
    forall s : S2508ResidueScheme ⟶ S2508AffineOver, s ≫ S2508ChartOverMap ≠ point

/-- **The missing datum of S2508 is exactly the boundary point and its
separation**: the representable open immersion of the chart map is supplied by
this file. -/
theorem S2512Missing_iff : S2508Missing ↔ S2512RemainingInput := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.point, D.separation⟩
  · rintro ⟨point, separation⟩
    exact ⟨S2512CuspDatumOf point separation⟩

/-! ## 8. Target-locked type checks -/

example : Iut.EtaleStackOpenImmersion S2508StackOpenMap := S2512StackOpenImmersion

example (point : S2508ResidueScheme ⟶ S2508FOver)
    (separation : forall s : S2508ResidueScheme ⟶ S2508AffineOver,
      s ≫ S2508ChartOverMap ≠ point) :
    S2508CuspDatum := S2512CuspDatumOf point separation

example (T : Iut.SchemeOverField UB)
    (point : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor UB T) S2508Compactification.fiber) :
    EtaleStackBaseChangePresentation (F := UB)
      (source := S2495cK.stack) (target := S2508Compactification)
      S2508StackOpenMap T point :=
  S2512BaseChange T point

/-! ## 9. Axiom audit -/

#print axioms S2512Val_isoOfValEq
#print axioms S2512Witness
#print axioms S2512TwoPullbackWitness
#print axioms S2512BaseChange
#print axioms S2512Projection_isOpenImmersion
#print axioms S2512StackOpenImmersion
#print axioms S2512CuspDatumOf
#print axioms S2512Missing_iff

end LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
