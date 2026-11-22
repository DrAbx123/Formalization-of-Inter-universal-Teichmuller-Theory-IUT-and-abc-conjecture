import tmp.sheaf.xif.paper.S2508CuspDataUB
import tmp.sheaf.xif.paper.S1911RepresentableTwoPullbackActual
import tmp.sheaf.xif.paper.S1932BuildA
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2515TwoPullbackUBActual
open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

/-- 2-cells between strong transformations into a representable stack are subsingletons. -/
theorem S2515ModificationSubsingleton {W : Iut.EtaleStackPseudofunctor UB}
    {P : Iut.SchemeOverField UB}
    (F G : Pseudofunctor.StrongTrans W (S1742YS (F := UB) P)) :
    Subsingleton (F ⟶ G) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact S1932NatTransSubsingleton (Discrete.isDiscrete _) (F.app U) (G.app U) |>.elim _ _

/-! ## 2. Values of a strong transformation into a representable stack -/

section Values

variable {W : EtaleStackPseudofunctor UB} {T : SchemeOverField UB}

/-- The value of a strong transformation into a representable etale stack, at a test
object and an object of the source fibre: the underlying morphism of schemes. -/
noncomputable def S2515Val (L : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) T))
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) : U.as.unop ⟶ T :=
  ((L.app U).toFunctor.obj a).as

/-- The defining computation rule of `S2515Val`. -/
@[simp] theorem S2515Val_def (L : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) T))
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    S2515Val L U a = ((L.app U).toFunctor.obj a).as := rfl

/-- The component of a vertical composite is the composite of the components. -/
theorem S2515App_vcomp {X Z : SchemeOverField UB}
    (L : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) X))
    (M : Pseudofunctor.StrongTrans ((S1742YS (F := UB)) X) ((S1742YS (F := UB)) Z))
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp L M).app U = L.app U ≫ M.app U := rfl

/-- Composition with a strong transformation of representable stacks acts on values by
composition of scheme morphisms. -/
theorem S2515Val_vcomp {X Z : SchemeOverField UB}
    (L : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) X))
    (M : Pseudofunctor.StrongTrans ((S1742YS (F := UB)) X) ((S1742YS (F := UB)) Z))
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    S2515Val (Pseudofunctor.StrongTrans.vcomp L M) U a =
      S2515Val L U a ≫ S1742HomOfStrongTrans (F := UB) M := by
  rw [S2515Val_def, S2515Val_def, S2515App_vcomp, S1742Comp_toFunctor_obj,
    ← S1742AppEq (F := UB) M U, ← Discrete.mk_as ((L.app U).toFunctor.obj a),
    S1742App_obj (F := UB) (S1742HomOfStrongTrans (F := UB) M) U]

/-- The value of a strong transformation into a representable stack is natural. -/
theorem S2515Val_naturality (L : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) T))
    {a b : LocallyDiscrete (SchemeOverField UB)ᵒᵖ} (φ : a ⟶ b) (x : W.obj a) :
    S2515Val L b ((W.map φ).toFunctor.obj x) = φ.as.unop ≫ S2515Val L a x := by
  rw [S2515Val_def, S2515Val_def]
  have h := Discrete.eq_of_hom ((L.naturality φ).hom.toNatTrans.app x)
  rw [S1742Comp_toFunctor_obj, S1742Comp_toFunctor_obj, S1742YS_map (F := UB) T φ,
    ← Discrete.mk_as ((L.app a).toFunctor.obj x), S1742Fiber_map_obj] at h
  exact h

end Values


/-! ## 3. The cone condition -/

section ConeCondition

variable {X Y Z P : SchemeOverField UB}

/-- The underlying scheme morphism of the first base leg of a square of representable
stacks. -/
noncomputable def S2515BaseF
    (sq : EtalePseudofunctorSquare ((S1742YS (F := UB)) P) ((S1742YS (F := UB)) X) ((S1742YS (F := UB)) Y) ((S1742YS (F := UB)) Z)) : X ⟶ Z :=
  S1742HomOfStrongTrans (F := UB) sq.xToBase

/-- The underlying scheme morphism of the second base leg of a square of representable
stacks. -/
noncomputable def S2515BaseG
    (sq : EtalePseudofunctorSquare ((S1742YS (F := UB)) P) ((S1742YS (F := UB)) X) ((S1742YS (F := UB)) Y) ((S1742YS (F := UB)) Z)) : Y ⟶ Z :=
  S1742HomOfStrongTrans (F := UB) sq.yToBase

/-- **The cone condition.**  For a cone over the square, the two composites of the cone's
legs with the square's base legs agree on underlying scheme morphisms.  This is the
hypothesis of the pullback lift, read off from the cone's 2-commutativity. -/
theorem S2515ConeCondition
    {sq : EtalePseudofunctorSquare ((S1742YS (F := UB)) P) ((S1742YS (F := UB)) X) ((S1742YS (F := UB)) Y) ((S1742YS (F := UB)) Z)}
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    S2515Val c.toX U a ≫ S2515BaseF sq = S2515Val c.toY U a ≫ S2515BaseG sq := by
  have h := Discrete.eq_of_hom ((c.commutes.hom.as.app U).toNatTrans.app a)
  simpa only [S2515BaseF, S2515BaseG, ← S2515Val_def, S2515Val_vcomp] using h

end ConeCondition

/-! ## 4. The lift of a cone, pointwise by pullback.lift -/

section Lift

variable {X Y Z P : SchemeOverField UB} {pX : P ⟶ X} {pY : P ⟶ Y}
variable {sq : EtalePseudofunctorSquare ((S1742YS (F := UB)) P) ((S1742YS (F := UB)) X) ((S1742YS (F := UB)) Y) ((S1742YS (F := UB)) Z)}

/-- The cone condition, on underlying scheme morphisms. -/
theorem S2515ConeCondition_left
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    (S2515Val c.toX U a).left ≫ (S2515BaseF sq).left =
      (S2515Val c.toY U a).left ≫ (S2515BaseG sq).left :=
  congrArg Over.Hom.left (S2515ConeCondition c U a)

/-- The underlying scheme morphism of the pullback lift of a cone. -/
noncomputable def S2515LiftSchemeVal
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    U.as.unop.left ⟶ P.left :=
  hpb.lift (S2515Val c.toX U a).left (S2515Val c.toY U a).left
    (S2515ConeCondition_left c U a)

/-- It projects to the first leg of the cone. -/
theorem S2515LiftSchemeVal_fst
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    S2515LiftSchemeVal hpb c U a ≫ pX.left = (S2515Val c.toX U a).left :=
  IsPullback.lift_fst hpb _ _ _

/-- It projects to the second leg of the cone. -/
theorem S2515LiftSchemeVal_snd
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    S2515LiftSchemeVal hpb c U a ≫ pY.left = (S2515Val c.toY U a).left :=
  IsPullback.lift_snd hpb _ _ _

/-- The pullback lift of a cone, as a morphism of schemes over the base. -/
noncomputable def S2515LiftVal
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) : U.as.unop ⟶ P :=
  Over.homMk (S2515LiftSchemeVal hpb c U a) (by
    rw [← pX.w, ← Category.assoc, S2515LiftSchemeVal_fst, (S2515Val c.toX U a).w])

/-- The lift projects to the first leg of the cone. -/
theorem S2515LiftVal_fst
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    S2515LiftVal hpb c U a ≫ pX = S2515Val c.toX U a := by
  apply Over.OverMorphism.ext
  show S2515LiftSchemeVal hpb c U a ≫ pX.left = (S2515Val c.toX U a).left
  exact S2515LiftSchemeVal_fst hpb c U a

/-- The lift projects to the second leg of the cone. -/
theorem S2515LiftVal_snd
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    S2515LiftVal hpb c U a ≫ pY = S2515Val c.toY U a := by
  apply Over.OverMorphism.ext
  show S2515LiftSchemeVal hpb c U a ≫ pY.left = (S2515Val c.toY U a).left
  exact S2515LiftSchemeVal_snd hpb c U a

/-- The first projection of the lift, on underlying scheme morphisms. -/
theorem S2515LiftVal_fst_left
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    Over.Hom.left (S2515LiftVal hpb c U a) ≫ pX.left = (S2515Val c.toX U a).left :=
  S2515LiftSchemeVal_fst hpb c U a

/-- The second projection of the lift, on underlying scheme morphisms. -/
theorem S2515LiftVal_snd_left
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    Over.Hom.left (S2515LiftVal hpb c U a) ≫ pY.left = (S2515Val c.toY U a).left :=
  S2515LiftSchemeVal_snd hpb c U a

/-- **The lift is well defined on the objects of the source fibre**: two objects joined by
a morphism have the same lift, because the two legs of the cone are functors into discrete
categories, and the pullback is a limit. -/
theorem S2515LiftVal_eq_of_hom
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ)
    {a b : W.obj U} (m : a ⟶ b) :
    S2515LiftVal hpb c U a = S2515LiftVal hpb c U b := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2515LiftVal hpb c U a) = Over.Hom.left (S2515LiftVal hpb c U b)
  apply IsPullback.hom_ext hpb
  · rw [S2515LiftVal_fst_left, S2515LiftVal_fst_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((c.toX.app U).toFunctor.map m))
  · rw [S2515LiftVal_snd_left, S2515LiftVal_snd_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((c.toY.app U).toFunctor.map m))

/-- The component functor of the lift at a test object. -/
noncomputable def S2515LiftFun
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) :
    ↑(W.obj U) ⥤ Discrete (U.as.unop ⟶ P) where
  obj a := Discrete.mk (S2515LiftVal hpb c U a)
  map m := Discrete.eqToHom (S2515LiftVal_eq_of_hom hpb c U m)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The value of the component functor. -/
theorem S2515LiftFun_obj
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    (S2515LiftFun hpb c U).obj a = Discrete.mk (S2515LiftVal hpb c U a) := rfl

/-- Naturality of the lift, on values. -/
theorem S2515LiftVal_naturality
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    {a b : LocallyDiscrete (SchemeOverField UB)ᵒᵖ} (φ : a ⟶ b) (x : W.obj a) :
    S2515LiftVal hpb c b ((W.map φ).toFunctor.obj x) =
      φ.as.unop ≫ S2515LiftVal hpb c a x := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2515LiftVal hpb c b ((W.map φ).toFunctor.obj x)) =
    Over.Hom.left (φ.as.unop ≫ S2515LiftVal hpb c a x)
  apply IsPullback.hom_ext hpb
  · simp only [Over.comp_left, Category.assoc, S2515LiftVal_fst_left]
    exact congrArg Over.Hom.left (S2515Val_naturality c.toX φ x)
  · simp only [Over.comp_left, Category.assoc, S2515LiftVal_snd_left]
    exact congrArg Over.Hom.left (S2515Val_naturality c.toY φ x)

/-- **Two strong transformations into a representable stack with equal values are
2-isomorphic.**  This is the form in which every comparison 2-cell of the lift is built. -/
theorem S2515Val_isoOfValEq {W : EtaleStackPseudofunctor UB}
    {T : SchemeOverField UB} {L L' : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) T)}
    (h : ∀ (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U),
      S2515Val L U a = S2515Val L' U a) :
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
noncomputable def S2515Lift
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    (W : EtaleStackPseudofunctor UB) (c : sq.Cone W) :
    Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) P) where
  app U := (S2515LiftFun hpb c U).toCatHom
  naturality {a b} φ := eqToIso (by
    apply Cat.ext
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro x
      show Discrete.mk (S2515LiftVal hpb c b ((W.map φ).toFunctor.obj x)) =
        (((S1742YS (F := UB)) P).map φ).toFunctor.obj (Discrete.mk (S2515LiftVal hpb c a x))
      rw [S1742YS_map (F := UB) P φ, S1742Fiber_map_obj]
      apply Discrete.ext
      show S2515LiftVal hpb c b ((W.map φ).toFunctor.obj x) =
        φ.as.unop ≫ S2515LiftVal hpb c a x
      exact S2515LiftVal_naturality hpb c φ x
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
noncomputable def S2515LiftToX
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    (W : EtaleStackPseudofunctor UB) (c : sq.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2515Lift hpb W c)
      (S1742StrongTransOfHom pX)) c.toX :=
  (S2515Val_isoOfValEq (fun U a => by
    rw [S2515Val_vcomp, S1742HomOfStrongTrans_strongTransOfHom]
    exact S2515LiftVal_fst hpb c U a)).some

/-- The lift compared with the second projection of the square. -/
noncomputable def S2515LiftToY
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    (W : EtaleStackPseudofunctor UB) (c : sq.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2515Lift hpb W c)
      (S1742StrongTransOfHom pY)) c.toY :=
  (S2515Val_isoOfValEq (fun U a => by
    rw [S2515Val_vcomp, S1742HomOfStrongTrans_strongTransOfHom]
    exact S2515LiftVal_snd hpb c U a)).some

/-- A morphism of cones induces the same lift, on values. -/
theorem S2515LiftVal_congr
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} {source target : sq.Cone W}
    (m : sq.ConeMorphism source target)
    (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U) :
    S2515LiftVal hpb source U a = S2515LiftVal hpb target U a := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2515LiftVal hpb source U a) =
    Over.Hom.left (S2515LiftVal hpb target U a)
  apply IsPullback.hom_ext hpb
  · rw [S2515LiftVal_fst_left, S2515LiftVal_fst_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((m.toX.as.app U).toNatTrans.app a))
  · rw [S2515LiftVal_snd_left, S2515LiftVal_snd_left]
    exact congrArg Over.Hom.left
      (Discrete.eq_of_hom ((m.toY.as.app U).toNatTrans.app a))

/-- The action of the lift on morphisms of cones. -/
noncomputable def S2515LiftIso
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    {W : EtaleStackPseudofunctor UB} {source target : sq.Cone W}
    (m : sq.ConeMorphism source target) :
    Iso (S2515Lift hpb W source) (S2515Lift hpb W target) :=
  (S2515Val_isoOfValEq (L := S2515Lift hpb W source) (L' := S2515Lift hpb W target)
    (fun U a => by
      show S2515LiftVal hpb source U a = S2515LiftVal hpb target U a
      exact S2515LiftVal_congr hpb m U a)).some

end Lift

/-! ## 5. The bicategorical pullback witness and its full 2-universal property -/

section Witness

variable {X Y Z P : SchemeOverField UB} {pX : P ⟶ X} {pY : P ⟶ Y}
variable {sq : EtalePseudofunctorSquare ((S1742YS (F := UB)) P) ((S1742YS (F := UB)) X) ((S1742YS (F := UB)) Y) ((S1742YS (F := UB)) Z)}

/-- **The square is a bicategorical pullback.**  The lift is the pointwise pullback lift;
the comparison 2-cells are subsingleton eliminations; the action on cone morphisms and
2-cell extensionality exist because 2-cells into a representable stack are subsingletons. -/
noncomputable def S2515Witness
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    (hX : sq.toX = S1742StrongTransOfHom pX)
    (hY : sq.toY = S1742StrongTransOfHom pY) : sq.TwoPullbackWitness where
  lift W c := S2515Lift hpb W c
  liftToX W c := by
    rw [hX]
    exact S2515LiftToX hpb W c
  liftToY W c := by
    rw [hY]
    exact S2515LiftToY hpb W c
  liftTwoCell W source target m := (S2515LiftIso hpb m).hom
  liftTwoCell_toX := by
    intro W source target m
    exact (S2515ModificationSubsingleton _ _).elim _ _
  liftTwoCell_toY := by
    intro W source target m
    exact (S2515ModificationSubsingleton _ _).elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    exact (S2515ModificationSubsingleton first second).elim alpha beta

/-- The cone condition of an arbitrary 1-cell into the pullback. -/
theorem S2515ConeEssSurj_cond
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) P))
    (h1 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX)) :
    ∀ (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U),
      S2515Val phi U a ≫ S1742HomOfStrongTrans sq.toX = S2515Val c.toX U a := by
  intro U a
  obtain ⟨e⟩ := h1
  have h := Discrete.eq_of_hom ((e.hom.as.app U).toNatTrans.app a)
  simpa only [← S2515Val_def, S2515Val_vcomp] using h

/-- The second cone condition of an arbitrary 1-cell into the pullback. -/
theorem S2515ConeEssSurj_condY
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) P))
    (h2 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY)) :
    ∀ (U : LocallyDiscrete (SchemeOverField UB)ᵒᵖ) (a : W.obj U),
      S2515Val phi U a ≫ S1742HomOfStrongTrans sq.toY = S2515Val c.toY U a := by
  intro U a
  obtain ⟨e⟩ := h2
  have h := Discrete.eq_of_hom ((e.hom.as.app U).toNatTrans.app a)
  simpa only [← S2515Val_def, S2515Val_vcomp] using h

/-- **The full 2-universal property of the square**: any 1-cell into the pullback whose
projections are 2-isomorphic to the cone's projections is 2-isomorphic to the lift. -/
theorem S2515ConeEssSurj
    (hpb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left)
    (hX : sq.toX = S1742StrongTransOfHom pX)
    (hY : sq.toY = S1742StrongTransOfHom pY)
    {W : EtaleStackPseudofunctor UB} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) P))
    (h1 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX))
    (h2 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY)) :
    Nonempty (Iso phi (S2515Lift hpb W c)) := by
  have hXc := S2515ConeEssSurj_cond c phi h1
  have hYc := S2515ConeEssSurj_condY c phi h2
  have hX' : S1742HomOfStrongTrans sq.toX = pX := by
    rw [hX, S1742HomOfStrongTrans_strongTransOfHom]
  have hY' : S1742HomOfStrongTrans sq.toY = pY := by
    rw [hY, S1742HomOfStrongTrans_strongTransOfHom]
  refine S2515Val_isoOfValEq (fun U a => ?_)
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2515Val phi U a) = Over.Hom.left (S2515LiftVal hpb c U a)
  apply IsPullback.hom_ext hpb
  · rw [S2515LiftVal_fst_left]
    rw [hX'] at hXc
    exact congrArg Over.Hom.left (hXc U a)
  · rw [S2515LiftVal_snd_left]
    rw [hY'] at hYc
    exact congrArg Over.Hom.left (hYc U a)

end Witness


/-! ## 6. The corrected statement, and what remains -/

/-- **The corrected form of the missing geometric input of S1897.**  For a *fibre-product*
square of schemes over `F'`, the square of representable etale stacks is a bicategorical
pullback whose cone comparison is essentially surjective on 1-cells.  Unlike
`S1897RepresentableTwoPullback` (refuted in section 1) the square is required to be a
pullback square; this is exactly the hypothesis available in the inverse construction of
S1897, where the square is the scheme-theoretic fibre product of the structure morphism of
the cover with a scheme-valued point of the orbicurve stack, and it is also what the
pullback lift itself presupposes. -/
def S2515RepresentableTwoPullbackPullbackSquare : Prop :=
  ∀ (X Y Z P : SchemeOverField UB) (pX : P ⟶ X) (pY : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z),
    IsPullback pX.left pY.left f.left g.left →
    ∀ (sq : EtalePseudofunctorSquare ((S1742YS (F := UB)) P) ((S1742YS (F := UB)) X) ((S1742YS (F := UB)) Y) ((S1742YS (F := UB)) Z)),
      sq.xToBase = S1742StrongTransOfHom f →
      sq.yToBase = S1742StrongTransOfHom g →
      sq.toX = S1742StrongTransOfHom pX →
      sq.toY = S1742StrongTransOfHom pY →
      ∃ w : sq.TwoPullbackWitness,
        ∀ (W : EtaleStackPseudofunctor UB) (c : sq.Cone W)
          (phi : Pseudofunctor.StrongTrans W ((S1742YS (F := UB)) P)),
          Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX) →
          Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY) →
          Nonempty (Iso phi (w.lift W c))

/-- **The corrected two-pullback theorem.** -/
theorem S2515RepresentableTwoPullbackPullbackSquare_proof :
    S2515RepresentableTwoPullbackPullbackSquare := by
  intro X Y Z P pX pY f g hpb sq hxb hyb hX hY
  have hF : S2515BaseF sq = f := by
    rw [S2515BaseF, hxb, S1742HomOfStrongTrans_strongTransOfHom]
  have hG : S2515BaseG sq = g := by
    rw [S2515BaseG, hyb, S1742HomOfStrongTrans_strongTransOfHom]
  have hb : IsPullback pX.left pY.left (S2515BaseF sq).left (S2515BaseG sq).left := by
    rw [hF, hG]
    exact hpb
  exact ⟨S2515Witness hb hX hY, fun W c phi h1 h2 =>
    S2515ConeEssSurj hb hX hY c phi h1 h2⟩

/-! ## 7. Checks and axiom footprint -/

#check S2515EmptyOver
#check S2515EmptySquare
#check S2515_not_representableTwoPullback
#check S2515Val
#check S2515Val_vcomp
#check S2515Val_naturality
#check S2515ConeCondition
#check S2515ConeCondition_left
#check S2515LiftSchemeVal
#check S2515LiftVal
#check S2515LiftVal_fst
#check S2515LiftVal_eq_of_hom
#check S2515LiftFun
#check S2515LiftVal_naturality
#check S2515Val_isoOfValEq
#check S2515Lift
#check S2515LiftToX
#check S2515LiftToY
#check S2515LiftIso
#check S2515Witness
#check S2515ConeEssSurj_cond
#check S2515ConeEssSurj
#check S2515RepresentableTwoPullbackPullbackSquare
#check S2515RepresentableTwoPullbackPullbackSquare_proof

#print axioms S2515_not_representableTwoPullback
#print axioms S2515Val_vcomp
#print axioms S2515ConeCondition
#print axioms S2515LiftVal_eq_of_hom
#print axioms S2515Val_isoOfValEq
#print axioms S2515Lift
#print axioms S2515Witness
#print axioms S2515ConeEssSurj
#print axioms S2515RepresentableTwoPullbackPullbackSquare_proof

end LeanFormal.IUT.XiFPaper.S2515RepresentableTwoPullbackActual

end LeanFormal.IUT.XiFPaper.S2515TwoPullbackUBActual
end
