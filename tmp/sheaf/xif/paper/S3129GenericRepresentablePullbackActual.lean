import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S2812IsStackActual
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3129GenericRepresentablePullbackActual

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

variable {F : Type} [Field F]

/-- Natural transformations between functors into a discrete category are
subsingletons. -/
theorem S3129NatTrans_discrete_subsingleton {D : Type*} [Category D] {alpha : Type}
    (G H : D ⥤ Discrete alpha) : Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply CategoryTheory.NatTrans.ext
  funext Z
  exact Subsingleton.elim _ _

/-- Modifications between strong transformations into a representable etale stack
are subsingletons. -/
theorem S3129Modification_subsingleton_representable
    {W : EtaleStackPseudofunctor F} {T : Iut.SchemeOverField F}
    (L L' : W ⟶ Iut.schemeRepresentableEtalePseudofunctor F T) :
    Subsingleton (L ⟶ L') := by
  constructor
  intro a b
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  apply CategoryTheory.Cat.Hom₂.ext
  haveI : Subsingleton ((L.app U).toFunctor ⟶ (L'.app U).toFunctor) :=
    S3129NatTrans_discrete_subsingleton _ _
  exact Subsingleton.elim _ _

/-! ## 2. Values of a strong transformation into a representable stack -/

section Values

variable {W : EtaleStackPseudofunctor F} {T : SchemeOverField F}

/-- The value of a strong transformation into a representable etale stack, at a test
object and an object of the source fibre: the underlying morphism of schemes. -/
noncomputable def S1911Val (L : Pseudofunctor.StrongTrans W (S1742YS T))
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) : U.as.unop ⟶ T :=
  ((L.app U).toFunctor.obj a).as

/-- The defining computation rule of `S1911Val`. -/
@[simp] theorem S1911Val_def (L : Pseudofunctor.StrongTrans W (S1742YS T))
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S1911Val L U a = ((L.app U).toFunctor.obj a).as := rfl

/-- The component of a vertical composite is the composite of the components. -/
theorem S1911App_vcomp {X Z : SchemeOverField F}
    (L : Pseudofunctor.StrongTrans W (S1742YS X))
    (M : Pseudofunctor.StrongTrans (S1742YS X) (S1742YS Z))
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp L M).app U = L.app U ≫ M.app U := rfl

/-- Composition with a strong transformation of representable stacks acts on values by
composition of scheme morphisms. -/
theorem S1911Val_vcomp {X Z : SchemeOverField F}
    (L : Pseudofunctor.StrongTrans W (S1742YS X))
    (M : Pseudofunctor.StrongTrans (S1742YS X) (S1742YS Z))
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S1911Val (Pseudofunctor.StrongTrans.vcomp L M) U a =
      S1911Val L U a ≫ S1742HomOfStrongTrans (F := F) M := by
  rw [S1911Val_def, S1911Val_def, S1911App_vcomp, S1742Comp_toFunctor_obj,
    ← S1742AppEq (F := F) M U, ← Discrete.mk_as ((L.app U).toFunctor.obj a),
    S1742App_obj (F := F) (S1742HomOfStrongTrans (F := F) M) U]

/-- The value of a strong transformation into a representable stack is natural. -/
theorem S1911Val_naturality (L : Pseudofunctor.StrongTrans W (S1742YS T))
    {a b : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (φ : a ⟶ b) (x : W.obj a) :
    S1911Val L b ((W.map φ).toFunctor.obj x) = φ.as.unop ≫ S1911Val L a x := by
  rw [S1911Val_def, S1911Val_def]
  have h := Discrete.eq_of_hom ((L.naturality φ).hom.toNatTrans.app x)
  rw [S1742Comp_toFunctor_obj, S1742Comp_toFunctor_obj, S1742YS_map (F := F) T φ,
    ← Discrete.mk_as ((L.app a).toFunctor.obj x), S1742Fiber_map_obj] at h
  exact h

end Values


/-! ## 3. The cone condition -/

section ConeCondition

variable {X Y Z P : SchemeOverField F}

/-- The underlying scheme morphism of the first base leg of a square of representable
stacks. -/
noncomputable def S1911BaseF
    (sq : EtalePseudofunctorSquare (S1742YS P) (S1742YS X) (S1742YS Y) (S1742YS Z)) : X ⟶ Z :=
  S1742HomOfStrongTrans (F := F) sq.xToBase

/-- The underlying scheme morphism of the second base leg of a square of representable
stacks. -/
noncomputable def S1911BaseG
    (sq : EtalePseudofunctorSquare (S1742YS P) (S1742YS X) (S1742YS Y) (S1742YS Z)) : Y ⟶ Z :=
  S1742HomOfStrongTrans (F := F) sq.yToBase

/-- **The cone condition.**  For a cone over the square, the two composites of the cone's
legs with the square's base legs agree on underlying scheme morphisms.  This is the
hypothesis of the pullback lift, read off from the cone's 2-commutativity. -/
theorem S1911ConeCondition
    {sq : EtalePseudofunctorSquare (S1742YS P) (S1742YS X) (S1742YS Y) (S1742YS Z)}
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S1911Val c.toX U a ≫ S1911BaseF sq = S1911Val c.toY U a ≫ S1911BaseG sq := by
  have h := Discrete.eq_of_hom ((c.commutes.hom.as.app U).toNatTrans.app a)
  simpa only [S1911BaseF, S1911BaseG, ← S1911Val_def, S1911Val_vcomp] using h

end ConeCondition

/-! ## 4. The lift of a cone, pointwise by pullback.lift -/

section Lift

variable {X Y Z P : SchemeOverField F} {pX : P ⟶ X} {pY : P ⟶ Y}
variable {sq : EtalePseudofunctorSquare (S1742YS P) (S1742YS X) (S1742YS Y) (S1742YS Z)}

/-- The cone condition, on underlying scheme morphisms. -/
theorem S1911ConeCondition_left
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    (S1911Val c.toX U a).left ≫ (S1911BaseF sq).left =
      (S1911Val c.toY U a).left ≫ (S1911BaseG sq).left :=
  congrArg Over.Hom.left (S1911ConeCondition c U a)

/-- The underlying scheme morphism of the pullback lift of a cone. -/
noncomputable def S1911LiftSchemeVal
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    U.as.unop.left ⟶ P.left :=
  hpb.lift (S1911Val c.toX U a).left (S1911Val c.toY U a).left
    (S1911ConeCondition_left c U a)

/-- It projects to the first leg of the cone. -/
theorem S1911LiftSchemeVal_fst
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S1911LiftSchemeVal hpb c U a ≫ pX.left = (S1911Val c.toX U a).left :=
  IsPullback.lift_fst hpb _ _ _

/-- It projects to the second leg of the cone. -/
theorem S1911LiftSchemeVal_snd
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S1911LiftSchemeVal hpb c U a ≫ pY.left = (S1911Val c.toY U a).left :=
  IsPullback.lift_snd hpb _ _ _

/-- The pullback lift of a cone, as a morphism of schemes over the base. -/
noncomputable def S1911LiftVal
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) : U.as.unop ⟶ P :=
  Over.homMk (S1911LiftSchemeVal hpb c U a) (by
    rw [← pX.w, ← Category.assoc, S1911LiftSchemeVal_fst, (S1911Val c.toX U a).w])

/-- The lift projects to the first leg of the cone. -/
theorem S1911LiftVal_fst
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S1911LiftVal hpb c U a ≫ pX = S1911Val c.toX U a := by
  apply Over.OverMorphism.ext
  show S1911LiftSchemeVal hpb c U a ≫ pX.left = (S1911Val c.toX U a).left
  exact S1911LiftSchemeVal_fst hpb c U a

/-- The lift projects to the second leg of the cone. -/
theorem S1911LiftVal_snd
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S1911LiftVal hpb c U a ≫ pY = S1911Val c.toY U a := by
  apply Over.OverMorphism.ext
  show S1911LiftSchemeVal hpb c U a ≫ pY.left = (S1911Val c.toY U a).left
  exact S1911LiftSchemeVal_snd hpb c U a

/-- The first projection of the lift, on underlying scheme morphisms. -/
theorem S1911LiftVal_fst_left
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    Over.Hom.left (S1911LiftVal hpb c U a) ≫ pX.left = (S1911Val c.toX U a).left :=
  S1911LiftSchemeVal_fst hpb c U a

/-- The second projection of the lift, on underlying scheme morphisms. -/
theorem S1911LiftVal_snd_left
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    Over.Hom.left (S1911LiftVal hpb c U a) ≫ pY.left = (S1911Val c.toY U a).left :=
  S1911LiftSchemeVal_snd hpb c U a

/-- **The lift is well defined on the objects of the source fibre**: two objects joined by
a morphism have the same lift, because the two legs of the cone are functors into discrete
categories, and the pullback is a limit. -/
theorem S1911LiftVal_eq_of_hom
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ)
    {a b : W.obj U} (m : a ⟶ b) :
    S1911LiftVal hpb c U a = S1911LiftVal hpb c U b := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S1911LiftVal hpb c U a) = Over.Hom.left (S1911LiftVal hpb c U b)
  apply IsPullback.hom_ext hpb
  · rw [S1911LiftVal_fst_left, S1911LiftVal_fst_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((c.toX.app U).toFunctor.map m))
  · rw [S1911LiftVal_snd_left, S1911LiftVal_snd_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((c.toY.app U).toFunctor.map m))

/-- The component functor of the lift at a test object. -/
noncomputable def S1911LiftFun
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    ↑(W.obj U) ⥤ Discrete (U.as.unop ⟶ P) where
  obj a := Discrete.mk (S1911LiftVal hpb c U a)
  map m := Discrete.eqToHom (S1911LiftVal_eq_of_hom hpb c U m)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The value of the component functor. -/
theorem S1911LiftFun_obj
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    (S1911LiftFun hpb c U).obj a = Discrete.mk (S1911LiftVal hpb c U a) := rfl

/-- Naturality of the lift, on values. -/
theorem S1911LiftVal_naturality
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    {a b : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (φ : a ⟶ b) (x : W.obj a) :
    S1911LiftVal hpb c b ((W.map φ).toFunctor.obj x) =
      φ.as.unop ≫ S1911LiftVal hpb c a x := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S1911LiftVal hpb c b ((W.map φ).toFunctor.obj x)) =
    Over.Hom.left (φ.as.unop ≫ S1911LiftVal hpb c a x)
  apply IsPullback.hom_ext hpb
  · simp only [Over.comp_left, Category.assoc, S1911LiftVal_fst_left]
    exact congrArg Over.Hom.left (S1911Val_naturality c.toX φ x)
  · simp only [Over.comp_left, Category.assoc, S1911LiftVal_snd_left]
    exact congrArg Over.Hom.left (S1911Val_naturality c.toY φ x)

/-- **Two strong transformations into a representable stack with equal values are
2-isomorphic.**  This is the form in which every comparison 2-cell of the lift is built. -/
theorem S1911Val_isoOfValEq {W : EtaleStackPseudofunctor F}
    {T : SchemeOverField F} {L L' : Pseudofunctor.StrongTrans W (S1742YS T)}
    (h : ∀ (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U),
      S1911Val L U a = S1911Val L' U a) :
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

/-- The lift of a cone as a strong transformation into the representable stack of the
apex. -/
noncomputable def S1911Lift
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    (W : EtaleStackPseudofunctor F) (c : sq.Cone W) :
    Pseudofunctor.StrongTrans W (S1742YS P) where
  app U := (S1911LiftFun hpb c U).toCatHom
  naturality {a b} φ := eqToIso (by
    apply Cat.ext
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro x
      show Discrete.mk (S1911LiftVal hpb c b ((W.map φ).toFunctor.obj x)) =
        ((S1742YS P).map φ).toFunctor.obj (Discrete.mk (S1911LiftVal hpb c a x))
      rw [S1742YS_map (F := F) P φ, S1742Fiber_map_obj]
      apply Discrete.ext
      show S1911LiftVal hpb c b ((W.map φ).toFunctor.obj x) =
        φ.as.unop ≫ S1911LiftVal hpb c a x
      exact S1911LiftVal_naturality hpb c φ x
    case h_map =>
      intro X Y f
      apply ULift.ext
      exact Subsingleton.elim _ _)
  naturality_naturality := by
    intro a b f g η
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
noncomputable def S1911LiftToX
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    (W : EtaleStackPseudofunctor F) (c : sq.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1911Lift hpb W c)
      (S1742StrongTransOfHom pX)) c.toX :=
  (S1911Val_isoOfValEq (fun U a => by
    rw [S1911Val_vcomp, S1742HomOfStrongTrans_strongTransOfHom]
    exact S1911LiftVal_fst hpb c U a)).some

/-- The lift compared with the second projection of the square. -/
noncomputable def S1911LiftToY
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    (W : EtaleStackPseudofunctor F) (c : sq.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1911Lift hpb W c)
      (S1742StrongTransOfHom pY)) c.toY :=
  (S1911Val_isoOfValEq (fun U a => by
    rw [S1911Val_vcomp, S1742HomOfStrongTrans_strongTransOfHom]
    exact S1911LiftVal_snd hpb c U a)).some

/-- A morphism of cones induces the same lift, on values. -/
theorem S1911LiftVal_congr
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} {source target : sq.Cone W}
    (m : sq.ConeMorphism source target)
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U) :
    S1911LiftVal hpb source U a = S1911LiftVal hpb target U a := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S1911LiftVal hpb source U a) =
    Over.Hom.left (S1911LiftVal hpb target U a)
  apply IsPullback.hom_ext hpb
  · rw [S1911LiftVal_fst_left, S1911LiftVal_fst_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((m.toX.as.app U).toNatTrans.app a))
  · rw [S1911LiftVal_snd_left, S1911LiftVal_snd_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((m.toY.as.app U).toNatTrans.app a))

/-- The action of the lift on morphisms of cones. -/
noncomputable def S1911LiftIso
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor F} {source target : sq.Cone W}
    (m : sq.ConeMorphism source target) :
    Iso (S1911Lift hpb W source) (S1911Lift hpb W target) :=
  (S1911Val_isoOfValEq (L := S1911Lift hpb W source) (L' := S1911Lift hpb W target)
    (fun U a => by
      show S1911LiftVal hpb source U a = S1911LiftVal hpb target U a
      exact S1911LiftVal_congr hpb m U a)).some

end Lift

/-! ## 5. The bicategorical pullback witness and its full 2-universal property -/

section Witness

variable {X Y Z P : SchemeOverField F} {pX : P ⟶ X} {pY : P ⟶ Y}
variable {sq : EtalePseudofunctorSquare (S1742YS P) (S1742YS X) (S1742YS Y) (S1742YS Z)}

/-- **The square is a bicategorical pullback.**  The lift is the pointwise pullback lift;
the comparison 2-cells are subsingleton eliminations; the action on cone morphisms and
2-cell extensionality exist because 2-cells into a representable stack are subsingletons. -/
noncomputable def S1911Witness
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    (hX : sq.toX = S1742StrongTransOfHom pX)
    (hY : sq.toY = S1742StrongTransOfHom pY) : sq.TwoPullbackWitness where
  lift W c := S1911Lift hpb W c
  liftToX W c := by
    rw [hX]
    exact S1911LiftToX hpb W c
  liftToY W c := by
    rw [hY]
    exact S1911LiftToY hpb W c
  liftTwoCell W source target m := (S1911LiftIso hpb m).hom
  liftTwoCell_toX := by
    intro W source target m
    exact (S3129Modification_subsingleton_representable _ _).elim _ _
  liftTwoCell_toY := by
    intro W source target m
    exact (S3129Modification_subsingleton_representable _ _).elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    exact (S3129Modification_subsingleton_representable first second).elim alpha beta

/-- The cone condition of an arbitrary 1-cell into the pullback. -/
theorem S1911ConeEssSurj_cond
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S1742YS P))
    (h1 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX)) :
    ∀ (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U),
      S1911Val phi U a ≫ S1742HomOfStrongTrans sq.toX = S1911Val c.toX U a := by
  intro U a
  obtain ⟨e⟩ := h1
  have h := Discrete.eq_of_hom ((e.hom.as.app U).toNatTrans.app a)
  simpa only [← S1911Val_def, S1911Val_vcomp] using h

/-- The second cone condition of an arbitrary 1-cell into the pullback. -/
theorem S1911ConeEssSurj_condY
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S1742YS P))
    (h2 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY)) :
    ∀ (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) (a : W.obj U),
      S1911Val phi U a ≫ S1742HomOfStrongTrans sq.toY = S1911Val c.toY U a := by
  intro U a
  obtain ⟨e⟩ := h2
  have h := Discrete.eq_of_hom ((e.hom.as.app U).toNatTrans.app a)
  simpa only [← S1911Val_def, S1911Val_vcomp] using h

/-- **The full 2-universal property of the square**: any 1-cell into the pullback whose
projections are 2-isomorphic to the cone's projections is 2-isomorphic to the lift. -/
theorem S1911ConeEssSurj
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    (hX : sq.toX = S1742StrongTransOfHom pX)
    (hY : sq.toY = S1742StrongTransOfHom pY)
    {W : EtaleStackPseudofunctor F} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S1742YS P))
    (h1 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX))
    (h2 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY)) :
    Nonempty (Iso phi (S1911Lift hpb W c)) := by
  have hXc := S1911ConeEssSurj_cond c phi h1
  have hYc := S1911ConeEssSurj_condY c phi h2
  have hX' : S1742HomOfStrongTrans sq.toX = pX := by
    rw [hX, S1742HomOfStrongTrans_strongTransOfHom]
  have hY' : S1742HomOfStrongTrans sq.toY = pY := by
    rw [hY, S1742HomOfStrongTrans_strongTransOfHom]
  refine S1911Val_isoOfValEq (fun U a => ?_)
  apply Over.OverMorphism.ext
  show Over.Hom.left (S1911Val phi U a) = Over.Hom.left (S1911LiftVal hpb c U a)
  apply IsPullback.hom_ext hpb
  · rw [S1911LiftVal_fst_left]
    rw [hX'] at hXc
    exact congrArg Over.Hom.left (hXc U a)
  · rw [S1911LiftVal_snd_left]
    rw [hY'] at hYc
    exact congrArg Over.Hom.left (hYc U a)

end Witness

end LeanFormal.IUT.XiFPaper.S3129GenericRepresentablePullbackActual
end