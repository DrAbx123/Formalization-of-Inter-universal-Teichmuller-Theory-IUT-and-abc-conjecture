/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1911
-/
import tmp.sheaf.xif.paper.S1897CoherentEssSurjActual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual

/-!
# S1911: the representable two-pullback theorem, and the refutation of its unbounded form

## The question

S1897 reduced S1878EssSurj to the named proposition

    S1897RepresentableTwoPullback : Prop

which asks, for *every* commutative square of schemes over F' with legs the Yoneda images
of scheme morphisms, for a `TwoPullbackWitness` of the induced square of representable
etale stacks, together with the full 2-universal property (S1852's `S1852ConeEssSurj`).
S1897 records this as the exact remaining geometric input of the inverse construction.

S1897's statement carries no fibre-product hypothesis: `P`, `pX`, `pY`, `f`, `g` are
arbitrary, and the only hypothesis relating them is the 2-commutative square `sq` itself
(equivalently, the commutativity of the underlying square of schemes).  That statement is
**false**, and section 1 proves it (`S1911_not_representableTwoPullback`): the square with
apex the empty scheme over `Spec F'` and all other vertices the affine base is commutative,
but a two-pullback witness would produce a strong transformation
`y(Spec R') -> y(empty)`, hence, by the 2-Yoneda comparison of S1742, an actual morphism
`Spec R' -> empty`, contradicting the nontriviality of the coordinate ring `R'`.

The mathematically correct statement is the one used by the inverse construction: the
square must be a genuine fibre-product square.  Sections 2-5 prove the theorem in that
form (`S1911CanonicalPullbackWitness`, `S1911CanonicalPullbackConeEssSurj`): for a
pullback square of schemes over `F'`, the square of representable etale stacks is a
bicategorical pullback with the full 2-universal property.  No hypothesis is added beyond
the fibre-product condition: the base legs of the stack square may be arbitrary strong
transformations of representable stacks, only their underlying scheme morphisms are
required to form the pullback (this is exactly what the base-change presentations of
S1852 need, where the point is an arbitrary scheme-valued point of the orbicurve stack,
not literally the Yoneda image of its 2-Yoneda evaluation).

## What is constructed

* Sections 2-3: the pointwise evaluation `S1911Val` of a strong transformation into a
  representable stack, its naturality (`S1911Val_naturality`), its compatibility with
  vertical composition with a transformation of representable stacks
  (`S1911Val_vcomp`), and the **cone condition** (`S1911ConeCondition`): for every cone
  over the square, the two composites of the cone's legs with the square's base legs agree
  on underlying scheme morphisms.

* Section 4: the lift `S1911Lift` of a cone, defined **pointwise by pullback.lift**
  (`S1911LiftVal`): on a test object `U` and an object `a` of the cone's source fibre, the
  value is the pullback lift of the pair of scheme morphisms given by the cone's two legs.
  Functoriality of the component is pullback uniqueness, naturality is pullback
  uniqueness plus the naturality of the cone's legs, and the three `StrongTrans`
  coherence fields are eliminated by `S1897Modification_subsingleton_representable`.

* Section 5: `S1911CanonicalPullbackWitness`, the `TwoPullbackWitness` for the square:
  lift, the two comparison 2-cells (`liftToX`, `liftToY`), the action on cone morphisms,
  and 2-cell extensionality (the last three are subsingleton eliminations, since the
  target is a representable stack).  `S1911CanonicalPullbackConeEssSurj` proves the full
  2-universal property: any 1-cell into the pullback whose two projections are
  2-isomorphic to the cone's projections agrees with the lift pointwise, by pullback
  uniqueness, and is therefore 2-isomorphic to it.

## Honest boundary

* No `sorry`, no new axiom, no `Shrink`/`ULift`/`PUnit`, no fake 2-cell: every 2-cell
  constructed here is built from actual scheme morphisms and pullback uniqueness; the
  subsingleton eliminations are the genuine discreteness of representable stacks.
* `S1911_not_representableTwoPullback` shows that the unbounded S1897 statement cannot be
  proved, so it is *not* a gap in this file: it is a false proposition, and the corrected
  statement proved here is what the base-change presentations require.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual
open LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-! ## 1. The unbounded S1897 statement is false -/

/-- The empty scheme, as a scheme over `Spec F'`. -/
noncomputable def S1911EmptyOver : SchemeOverField S1726K :=
  Over.mk (Scheme.emptyTo (Spec (CommRingCat.of S1726K)))

/-- The empty scheme over `Spec F'` maps to the affine base. -/
noncomputable def S1911EmptyToAffine : S1911EmptyOver ⟶ S1726AffineOver :=
  Over.homMk (Scheme.emptyTo S1726AffineScheme) (Scheme.empty_ext _ _)

/-- The square with apex the empty scheme: a commutative square whose apex is not the
fibre product. -/
noncomputable def S1911EmptySquare :
    EtalePseudofunctorSquare (S1897Y S1911EmptyOver) (S1897Y S1726AffineOver)
      (S1897Y S1726AffineOver) (S1897Y S1726AffineOver) where
  toX := S1742StrongTransOfHom S1911EmptyToAffine
  toY := S1742StrongTransOfHom S1911EmptyToAffine
  xToBase := S1742StrongTransOfHom (𝟙 S1726AffineOver)
  yToBase := S1742StrongTransOfHom (𝟙 S1726AffineOver)
  commutes := eqToIso rfl

/-- A cone over that square. -/
noncomputable def S1911EmptyCone :
    S1911EmptySquare.Cone (S1897Y S1726AffineOver) where
  toX := S1742StrongTransOfHom (𝟙 S1726AffineOver)
  toY := S1742StrongTransOfHom (𝟙 S1726AffineOver)
  commutes := eqToIso rfl

/-- **The literal S1897 statement is false.**  It asks for a two-pullback witness of the
Yoneda image of *every* commutative square of schemes over `F'`, with no
fibre-product hypothesis.  The square with apex the empty scheme and all three other
vertices the affine base is commutative, but a witness would produce a morphism
`Spec R' -> empty`, whose existence contradicts `R'` being nontrivial. -/
theorem S1911_not_representableTwoPullback : ¬ S1897RepresentableTwoPullback := by
  intro H
  obtain ⟨w, -⟩ := H S1726AffineOver S1726AffineOver S1726AffineOver S1911EmptyOver
    (𝟙 S1726AffineOver) (𝟙 S1726AffineOver) S1911EmptyToAffine S1911EmptyToAffine
    S1911EmptySquare rfl rfl rfl rfl
  have hlift : Pseudofunctor.StrongTrans (S1897Y S1726AffineOver) (S1897Y S1911EmptyOver) :=
    w.lift (S1897Y S1726AffineOver) S1911EmptyCone
  have hval : S1726AffineOver ⟶ S1911EmptyOver :=
    S1742HomOfStrongTrans (F := S1726K) hlift
  have hne : Nonempty S1726AffineScheme := by
    haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
    show Nonempty (Spec (CommRingCat.of S1726CoordinateRing))
    infer_instance
  obtain ⟨x⟩ := hne
  haveI : IsEmpty ↥(S1911EmptyOver.left) := by
    show IsEmpty (↥(∅ : Scheme))
    infer_instance
  exact isEmptyElim (hval.left.base.hom x)

/-! ## 2. Values of a strong transformation into a representable stack -/

section Values

variable {W : EtaleStackPseudofunctor S1726K} {T : SchemeOverField S1726K}

/-- The value of a strong transformation into a representable etale stack, at a test
object and an object of the source fibre: the underlying morphism of schemes. -/
noncomputable def S1911Val (L : Pseudofunctor.StrongTrans W (S1897Y T))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) : U.as.unop ⟶ T :=
  ((L.app U).toFunctor.obj a).as

/-- The defining computation rule of `S1911Val`. -/
@[simp] theorem S1911Val_def (L : Pseudofunctor.StrongTrans W (S1897Y T))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1911Val L U a = ((L.app U).toFunctor.obj a).as := rfl

/-- The component of a vertical composite is the composite of the components. -/
theorem S1911App_vcomp {X Z : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans W (S1897Y X))
    (M : Pseudofunctor.StrongTrans (S1897Y X) (S1897Y Z))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp L M).app U = L.app U ≫ M.app U := rfl

/-- Composition with a strong transformation of representable stacks acts on values by
composition of scheme morphisms. -/
theorem S1911Val_vcomp {X Z : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans W (S1897Y X))
    (M : Pseudofunctor.StrongTrans (S1897Y X) (S1897Y Z))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1911Val (Pseudofunctor.StrongTrans.vcomp L M) U a =
      S1911Val L U a ≫ S1742HomOfStrongTrans (F := S1726K) M := by
  rw [S1911Val_def, S1911Val_def, S1911App_vcomp, S1742Comp_toFunctor_obj,
    ← S1742AppEq (F := S1726K) M U, ← Discrete.mk_as ((L.app U).toFunctor.obj a),
    S1742App_obj (F := S1726K) (S1742HomOfStrongTrans (F := S1726K) M) U]

/-- The value of a strong transformation into a representable stack is natural. -/
theorem S1911Val_naturality (L : Pseudofunctor.StrongTrans W (S1897Y T))
    {a b : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : a ⟶ b) (x : W.obj a) :
    S1911Val L b ((W.map φ).toFunctor.obj x) = φ.as.unop ≫ S1911Val L a x := by
  rw [S1911Val_def, S1911Val_def]
  have h := Discrete.eq_of_hom ((L.naturality φ).hom.toNatTrans.app x)
  rw [S1742Comp_toFunctor_obj, S1742Comp_toFunctor_obj, S1742YS_map (F := S1726K) T φ,
    ← Discrete.mk_as ((L.app a).toFunctor.obj x), S1742Fiber_map_obj] at h
  exact h

end Values


/-! ## 3. The cone condition -/

section ConeCondition

variable {X Y Z P : SchemeOverField S1726K}

/-- The underlying scheme morphism of the first base leg of a square of representable
stacks. -/
noncomputable def S1911BaseF
    (sq : EtalePseudofunctorSquare (S1897Y P) (S1897Y X) (S1897Y Y) (S1897Y Z)) : X ⟶ Z :=
  S1742HomOfStrongTrans (F := S1726K) sq.xToBase

/-- The underlying scheme morphism of the second base leg of a square of representable
stacks. -/
noncomputable def S1911BaseG
    (sq : EtalePseudofunctorSquare (S1897Y P) (S1897Y X) (S1897Y Y) (S1897Y Z)) : Y ⟶ Z :=
  S1742HomOfStrongTrans (F := S1726K) sq.yToBase

/-- **The cone condition.**  For a cone over the square, the two composites of the cone's
legs with the square's base legs agree on underlying scheme morphisms.  This is the
hypothesis of the pullback lift, read off from the cone's 2-commutativity. -/
theorem S1911ConeCondition
    {sq : EtalePseudofunctorSquare (S1897Y P) (S1897Y X) (S1897Y Y) (S1897Y Z)}
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1911Val c.toX U a ≫ S1911BaseF sq = S1911Val c.toY U a ≫ S1911BaseG sq := by
  have h := Discrete.eq_of_hom ((c.commutes.hom.as.app U).toNatTrans.app a)
  simpa only [S1911BaseF, S1911BaseG, ← S1911Val_def, S1911Val_vcomp] using h

end ConeCondition

/-! ## 4. The lift of a cone, pointwise by pullback.lift -/

section Lift

variable {X Y Z P : SchemeOverField S1726K} {pX : P ⟶ X} {pY : P ⟶ Y}
variable {sq : EtalePseudofunctorSquare (S1897Y P) (S1897Y X) (S1897Y Y) (S1897Y Z)}

/-- The cone condition, on underlying scheme morphisms. -/
theorem S1911ConeCondition_left
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    (S1911Val c.toX U a).left ≫ (S1911BaseF sq).left =
      (S1911Val c.toY U a).left ≫ (S1911BaseG sq).left :=
  congrArg Over.Hom.left (S1911ConeCondition c U a)

/-- The underlying scheme morphism of the pullback lift of a cone. -/
noncomputable def S1911LiftSchemeVal
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    U.as.unop.left ⟶ P.left :=
  hpb.lift (S1911Val c.toX U a).left (S1911Val c.toY U a).left
    (S1911ConeCondition_left c U a)

/-- It projects to the first leg of the cone. -/
theorem S1911LiftSchemeVal_fst
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1911LiftSchemeVal hpb c U a ≫ pX.left = (S1911Val c.toX U a).left :=
  IsPullback.lift_fst hpb _ _ _

/-- It projects to the second leg of the cone. -/
theorem S1911LiftSchemeVal_snd
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1911LiftSchemeVal hpb c U a ≫ pY.left = (S1911Val c.toY U a).left :=
  IsPullback.lift_snd hpb _ _ _

/-- The pullback lift of a cone, as a morphism of schemes over the base. -/
noncomputable def S1911LiftVal
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) : U.as.unop ⟶ P :=
  Over.homMk (S1911LiftSchemeVal hpb c U a) (by
    rw [← pX.w, ← Category.assoc, S1911LiftSchemeVal_fst, (S1911Val c.toX U a).w])

/-- The lift projects to the first leg of the cone. -/
theorem S1911LiftVal_fst
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1911LiftVal hpb c U a ≫ pX = S1911Val c.toX U a := by
  apply Over.OverMorphism.ext
  show S1911LiftSchemeVal hpb c U a ≫ pX.left = (S1911Val c.toX U a).left
  exact S1911LiftSchemeVal_fst hpb c U a

/-- The lift projects to the second leg of the cone. -/
theorem S1911LiftVal_snd
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1911LiftVal hpb c U a ≫ pY = S1911Val c.toY U a := by
  apply Over.OverMorphism.ext
  show S1911LiftSchemeVal hpb c U a ≫ pY.left = (S1911Val c.toY U a).left
  exact S1911LiftSchemeVal_snd hpb c U a

/-- The first projection of the lift, on underlying scheme morphisms. -/
theorem S1911LiftVal_fst_left
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    Over.Hom.left (S1911LiftVal hpb c U a) ≫ pX.left = (S1911Val c.toX U a).left :=
  S1911LiftSchemeVal_fst hpb c U a

/-- The second projection of the lift, on underlying scheme morphisms. -/
theorem S1911LiftVal_snd_left
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    Over.Hom.left (S1911LiftVal hpb c U a) ≫ pY.left = (S1911Val c.toY U a).left :=
  S1911LiftSchemeVal_snd hpb c U a

/-- **The lift is well defined on the objects of the source fibre**: two objects joined by
a morphism have the same lift, because the two legs of the cone are functors into discrete
categories, and the pullback is a limit. -/
theorem S1911LiftVal_eq_of_hom
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
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
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    ↑(W.obj U) ⥤ Discrete (U.as.unop ⟶ P) where
  obj a := Discrete.mk (S1911LiftVal hpb c U a)
  map m := Discrete.eqToHom (S1911LiftVal_eq_of_hom hpb c U m)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The value of the component functor. -/
theorem S1911LiftFun_obj
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    (S1911LiftFun hpb c U).obj a = Discrete.mk (S1911LiftVal hpb c U a) := rfl

/-- Naturality of the lift, on values. -/
theorem S1911LiftVal_naturality
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    {a b : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : a ⟶ b) (x : W.obj a) :
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
theorem S1911Val_isoOfValEq {W : EtaleStackPseudofunctor S1726K}
    {T : SchemeOverField S1726K} {L L' : Pseudofunctor.StrongTrans W (S1897Y T)}
    (h : ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U),
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
    (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W) :
    Pseudofunctor.StrongTrans W (S1897Y P) where
  app U := (S1911LiftFun hpb c U).toCatHom
  naturality {a b} φ := eqToIso (by
    apply Cat.ext
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro x
      show Discrete.mk (S1911LiftVal hpb c b ((W.map φ).toFunctor.obj x)) =
        ((S1897Y P).map φ).toFunctor.obj (Discrete.mk (S1911LiftVal hpb c a x))
      rw [S1742YS_map (F := S1726K) P φ, S1742Fiber_map_obj]
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
    (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1911Lift hpb W c)
      (S1742StrongTransOfHom pX)) c.toX :=
  (S1911Val_isoOfValEq (fun U a => by
    rw [S1911Val_vcomp, S1742HomOfStrongTrans_strongTransOfHom]
    exact S1911LiftVal_fst hpb c U a)).some

/-- The lift compared with the second projection of the square. -/
noncomputable def S1911LiftToY
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1911Lift hpb W c)
      (S1742StrongTransOfHom pY)) c.toY :=
  (S1911Val_isoOfValEq (fun U a => by
    rw [S1911Val_vcomp, S1742HomOfStrongTrans_strongTransOfHom]
    exact S1911LiftVal_snd hpb c U a)).some

/-- A morphism of cones induces the same lift, on values. -/
theorem S1911LiftVal_congr
    (hpb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left)
    {W : EtaleStackPseudofunctor S1726K} {source target : sq.Cone W}
    (m : sq.ConeMorphism source target)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
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
    {W : EtaleStackPseudofunctor S1726K} {source target : sq.Cone W}
    (m : sq.ConeMorphism source target) :
    Iso (S1911Lift hpb W source) (S1911Lift hpb W target) :=
  (S1911Val_isoOfValEq (L := S1911Lift hpb W source) (L' := S1911Lift hpb W target)
    (fun U a => by
      show S1911LiftVal hpb source U a = S1911LiftVal hpb target U a
      exact S1911LiftVal_congr hpb m U a)).some

end Lift

/-! ## 5. The bicategorical pullback witness and its full 2-universal property -/

section Witness

variable {X Y Z P : SchemeOverField S1726K} {pX : P ⟶ X} {pY : P ⟶ Y}
variable {sq : EtalePseudofunctorSquare (S1897Y P) (S1897Y X) (S1897Y Y) (S1897Y Z)}

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
    exact (S1897Modification_subsingleton_representable _ _).elim _ _
  liftTwoCell_toY := by
    intro W source target m
    exact (S1897Modification_subsingleton_representable _ _).elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    exact (S1897Modification_subsingleton_representable first second).elim alpha beta

/-- The cone condition of an arbitrary 1-cell into the pullback. -/
theorem S1911ConeEssSurj_cond
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S1897Y P))
    (h1 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX)) :
    ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U),
      S1911Val phi U a ≫ S1742HomOfStrongTrans sq.toX = S1911Val c.toX U a := by
  intro U a
  obtain ⟨e⟩ := h1
  have h := Discrete.eq_of_hom ((e.hom.as.app U).toNatTrans.app a)
  simpa only [← S1911Val_def, S1911Val_vcomp] using h

/-- The second cone condition of an arbitrary 1-cell into the pullback. -/
theorem S1911ConeEssSurj_condY
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S1897Y P))
    (h2 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY)) :
    ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U),
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
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (phi : Pseudofunctor.StrongTrans W (S1897Y P))
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


/-! ## 6. The corrected statement, and what remains -/

/-- **The corrected form of the missing geometric input of S1897.**  For a *fibre-product*
square of schemes over `F'`, the square of representable etale stacks is a bicategorical
pullback whose cone comparison is essentially surjective on 1-cells.  Unlike
`S1897RepresentableTwoPullback` (refuted in section 1) the square is required to be a
pullback square; this is exactly the hypothesis available in the inverse construction of
S1897, where the square is the scheme-theoretic fibre product of the structure morphism of
the cover with a scheme-valued point of the orbicurve stack, and it is also what the
pullback lift itself presupposes. -/
def S1911RepresentableTwoPullbackPullbackSquare : Prop :=
  ∀ (X Y Z P : SchemeOverField S1726K) (pX : P ⟶ X) (pY : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z),
    IsPullback pX.left pY.left f.left g.left →
    ∀ (sq : EtalePseudofunctorSquare (S1897Y P) (S1897Y X) (S1897Y Y) (S1897Y Z)),
      sq.xToBase = S1742StrongTransOfHom f →
      sq.yToBase = S1742StrongTransOfHom g →
      sq.toX = S1742StrongTransOfHom pX →
      sq.toY = S1742StrongTransOfHom pY →
      ∃ w : sq.TwoPullbackWitness,
        ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W)
          (phi : Pseudofunctor.StrongTrans W (S1897Y P)),
          Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX) →
          Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY) →
          Nonempty (Iso phi (w.lift W c))

/-- **The corrected two-pullback theorem.** -/
theorem S1911RepresentableTwoPullbackPullbackSquare_proof :
    S1911RepresentableTwoPullbackPullbackSquare := by
  intro X Y Z P pX pY f g hpb sq hxb hyb hX hY
  have hF : S1911BaseF sq = f := by
    rw [S1911BaseF, hxb, S1742HomOfStrongTrans_strongTransOfHom]
  have hG : S1911BaseG sq = g := by
    rw [S1911BaseG, hyb, S1742HomOfStrongTrans_strongTransOfHom]
  have hb : IsPullback pX.left pY.left (S1911BaseF sq).left (S1911BaseG sq).left := by
    rw [hF, hG]
    exact hpb
  exact ⟨S1911Witness hb hX hY, fun W c phi h1 h2 =>
    S1911ConeEssSurj hb hX hY c phi h1 h2⟩

/-! ## 7. Checks and axiom footprint -/

#check S1911EmptyOver
#check S1911EmptySquare
#check S1911_not_representableTwoPullback
#check S1911Val
#check S1911Val_vcomp
#check S1911Val_naturality
#check S1911ConeCondition
#check S1911ConeCondition_left
#check S1911LiftSchemeVal
#check S1911LiftVal
#check S1911LiftVal_fst
#check S1911LiftVal_eq_of_hom
#check S1911LiftFun
#check S1911LiftVal_naturality
#check S1911Val_isoOfValEq
#check S1911Lift
#check S1911LiftToX
#check S1911LiftToY
#check S1911LiftIso
#check S1911Witness
#check S1911ConeEssSurj_cond
#check S1911ConeEssSurj
#check S1911RepresentableTwoPullbackPullbackSquare
#check S1911RepresentableTwoPullbackPullbackSquare_proof

#print axioms S1911_not_representableTwoPullback
#print axioms S1911Val_vcomp
#print axioms S1911ConeCondition
#print axioms S1911LiftVal_eq_of_hom
#print axioms S1911Val_isoOfValEq
#print axioms S1911Lift
#print axioms S1911Witness
#print axioms S1911ConeEssSurj
#print axioms S1911RepresentableTwoPullbackPullbackSquare_proof

end LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
