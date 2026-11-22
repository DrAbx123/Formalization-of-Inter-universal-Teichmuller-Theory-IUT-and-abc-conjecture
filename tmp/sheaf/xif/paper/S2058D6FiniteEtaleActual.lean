/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S2058
-/
import tmp.sheaf.xif.paper.S2044D6FiniteEtaleClosureActual
import tmp.sheaf.xif.paper.S1897CoherentEssSurjActual

/-!
# S2058: the D6(c) finite-etale API -- 2-isomorphism invariance (proved)

EtaleStackRepresentableMorphismProperty (Iut/Foundations/Orbicurve.lean) has no
composition or 2-isomorphism API.  This file builds it.

## What is proved here

* S2058WhiskerLeftIso, S2058WhiskerRightIso, S2058AssociatorIso: the bicategory
  isomorphisms of the pseudofunctor bicategory, in the shape needed below.
* S2058OldCone, S2058OldHom, S2058IsoWitness: 2-isomorphism invariance of the
  two-pullback witness.  Changing one base leg of a square along a
  2-isomorphism does not change toX, toY, liftToX, liftToY, liftTwoCell,
  liftTwoCell_toX, liftTwoCell_toY or twoCell_ext; the only new coherence input
  is the exchange law Bicategory.whisker_exchange in the action on cone
  morphisms.  No field is fabricated.
* S2058IsoInvarianceProperty: representable morphism properties are invariant
  under 2-isomorphism of the stack morphism.
* S2058IsoInvarianceFiniteEtale: the finite-etale specialization, which is
  S2046IsoInvarianceStatement of S2046 and S1892TransportHolds of S1892.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT

universe u

variable {F : Type u} [Field F]

/-! ## 1. Bicategory isomorphisms of the pseudofunctor bicategory -/

/-- Left whiskering of a 2-isomorphism by a strong transformation. -/
noncomputable def S2058WhiskerLeftIso {A B C : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g g' : Pseudofunctor.StrongTrans B C)
    (e : Iso g g') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g)
      (Pseudofunctor.StrongTrans.vcomp f g') :=
  Bicategory.whiskerLeftIso (B := EtaleStackPseudofunctor F) f e

/-- Right whiskering of a 2-isomorphism by a strong transformation. -/
noncomputable def S2058WhiskerRightIso {A B C : EtaleStackPseudofunctor F}
    (f f' : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (e : Iso f f') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g)
      (Pseudofunctor.StrongTrans.vcomp f' g) :=
  Bicategory.whiskerRightIso (B := EtaleStackPseudofunctor F) e g

/-- The associator of three composable strong transformations. -/
noncomputable def S2058AssociatorIso {A B C D : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (h : Pseudofunctor.StrongTrans C D) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp f g) h)
      (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.vcomp g h)) :=
  Bicategory.associator (B := EtaleStackPseudofunctor F) f g h

/-- Left whiskering of a 2-isomorphism, with the two 1-cells implicit. -/
noncomputable def S2058WhiskerLeft {A B C : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) {g g' : Pseudofunctor.StrongTrans B C}
    (e : Iso g g') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g)
      (Pseudofunctor.StrongTrans.vcomp f g') :=
  Bicategory.whiskerLeftIso (B := EtaleStackPseudofunctor F) f e

/-- Right whiskering of a 2-isomorphism, with the two 1-cells implicit. -/
noncomputable def S2058WhiskerRight {A B C : EtaleStackPseudofunctor F}
    {f f' : Pseudofunctor.StrongTrans A B} (e : Iso f f')
    (g : Pseudofunctor.StrongTrans B C) :
    Iso (Pseudofunctor.StrongTrans.vcomp f g)
      (Pseudofunctor.StrongTrans.vcomp f' g) :=
  Bicategory.whiskerRightIso (B := EtaleStackPseudofunctor F) e g

theorem S2058WhiskerLeftIso_hom {A B C : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g g' : Pseudofunctor.StrongTrans B C)
    (e : Iso g g') :
    (S2058WhiskerLeftIso f g g' e).hom =
      @Bicategory.whiskerLeft (EtaleStackPseudofunctor F) _ A B C f g g' e.hom := rfl

/-! ## 2. Transport of the two-pullback witness along a 2-isomorphism -/

/-- The cone of the square with first base leg x' seen as a cone of the square
with first base leg the 2-isomorphic x. -/
noncomputable def S2058OldCone {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y) (xi : Y ⟶ Z)
    {x x' : X ⟶ Z} (e : Iso x x')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi c').Cone W) :
    (EtalePseudofunctorSquare.mk toX toY x xi c).Cone W where
  toX := cone.toX
  toY := cone.toY
  commutes := (S2058WhiskerLeftIso cone.toX x x' e).trans cone.commutes

theorem S2058OldCone_toX {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y) (xi : Y ⟶ Z)
    {x x' : X ⟶ Z} (e : Iso x x')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi c').Cone W) :
    (S2058OldCone toX toY xi e c c' cone).toX = cone.toX := rfl

theorem S2058OldCone_toY {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y) (xi : Y ⟶ Z)
    {x x' : X ⟶ Z} (e : Iso x x')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi c').Cone W) :
    (S2058OldCone toX toY xi e c c' cone).toY = cone.toY := rfl

theorem S2058OldCone_commutes {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y) (xi : Y ⟶ Z)
    {x x' : X ⟶ Z} (e : Iso x x')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi c').Cone W) :
    (S2058OldCone toX toY xi e c c' cone).commutes =
      (S2058WhiskerLeftIso cone.toX x x' e).trans cone.commutes := rfl

/-- A morphism of cones of the square with first base leg x' induces a
morphism of the corresponding cones of the square with base leg x. -/
noncomputable def S2058OldHom {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y) (xi : Y ⟶ Z)
    {x x' : X ⟶ Z} (e : Iso x x')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    {W : EtaleStackPseudofunctor F}
    {s t : (EtalePseudofunctorSquare.mk toX toY x' xi c').Cone W}
    (m : (EtalePseudofunctorSquare.mk toX toY x' xi c').ConeMorphism s t) :
    (EtalePseudofunctorSquare.mk toX toY x xi c).ConeMorphism
      (S2058OldCone toX toY xi e c c' s)
      (S2058OldCone toX toY xi e c c' t) where
  toX := m.toX
  toY := m.toY
  compatibility := by
    rw [S2058OldCone_commutes, S2058OldCone_commutes, Iso.trans_hom, Iso.trans_hom,
      S2058WhiskerLeftIso_hom]
    have hsq : ((m.toX) ▷ x) ≫ (t.toX ◁ e.hom) =
        (s.toX ◁ e.hom) ≫ ((m.toX) ▷ x') := by
      rw [Bicategory.whisker_exchange]
    have hcompat : ((m.toX) ▷ x') ≫ t.commutes.hom =
        s.commutes.hom ≫ ((m.toY) ▷ xi) := m.compatibility
    calc
      ((m.toX) ▷ x) ≫ ((t.toX ◁ e.hom) ≫ t.commutes.hom)
          = (((m.toX) ▷ x) ≫ (t.toX ◁ e.hom)) ≫ t.commutes.hom := by
            rw [Category.assoc]
      _ = ((s.toX ◁ e.hom) ≫ ((m.toX) ▷ x')) ≫ t.commutes.hom := by rw [hsq]
      _ = (s.toX ◁ e.hom) ≫ (((m.toX) ▷ x') ≫ t.commutes.hom) := by
            rw [Category.assoc]
      _ = (s.toX ◁ e.hom) ≫ (s.commutes.hom ≫ ((m.toY) ▷ xi)) := by
            rw [hcompat]
      _ = ((s.toX ◁ e.hom) ≫ s.commutes.hom) ≫ ((m.toY) ▷ xi) := by
            rw [Category.assoc]

/-- 2-isomorphism invariance of the two-pullback witness: if a square is a
bicategorical pullback, so is the square obtained by replacing its first base
leg by a 2-isomorphic one. -/
noncomputable def S2058IsoWitness {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y) (xi : Y ⟶ Z)
    {x x' : X ⟶ Z} (e : Iso x x')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (w : (EtalePseudofunctorSquare.mk toX toY x xi c).TwoPullbackWitness) :
    (EtalePseudofunctorSquare.mk toX toY x' xi c').TwoPullbackWitness where
  lift W cone := w.lift W (S2058OldCone toX toY xi e c c' cone)
  liftToX W cone := w.liftToX W (S2058OldCone toX toY xi e c c' cone)
  liftToY W cone := w.liftToY W (S2058OldCone toX toY xi e c c' cone)
  liftTwoCell W s t m :=
    w.liftTwoCell W (S2058OldCone toX toY xi e c c' s)
      (S2058OldCone toX toY xi e c c' t) (S2058OldHom toX toY xi e c c' m)
  liftTwoCell_toX W s t m :=
    w.liftTwoCell_toX W (S2058OldCone toX toY xi e c c' s)
      (S2058OldCone toX toY xi e c c' t) (S2058OldHom toX toY xi e c c' m)
  liftTwoCell_toY W s t m :=
    w.liftTwoCell_toY W (S2058OldCone toX toY xi e c c' s)
      (S2058OldCone toX toY xi e c c' t) (S2058OldHom toX toY xi e c c' m)
  twoCell_ext W first second alpha beta h1 h2 :=
    w.twoCell_ext W (first := first) (second := second) alpha beta h1 h2

/-! ## 3. 2-isomorphism invariance of representable morphism properties -/

/-- Representable morphism properties are invariant under 2-isomorphism of the
stack morphism.  The base-change presentation, and in particular the
scheme-theoretic projection, is kept exactly; only the horizontal leg of every
base-change square is replaced by the 2-isomorphic one. -/
noncomputable def S2058IsoInvarianceProperty
    (P : forall {S T : Scheme.{u}}, (S ⟶ T) -> Prop)
    {X Z : EtaleStackOverField F} {p q : X.Hom Z} (e : Iso p q)
    (h : EtaleStackRepresentableMorphismProperty P p) :
    EtaleStackRepresentableMorphismProperty P q where
  baseChange T point :=
    { pullbackScheme := (h.baseChange T point).pullbackScheme
      projection := (h.baseChange T point).projection
      projectionMap := (h.baseChange T point).projectionMap
      toSource := (h.baseChange T point).toSource
      commutes :=
        (S2058WhiskerLeftIso (h.baseChange T point).toSource p q e).symm.trans
          (h.baseChange T point).commutes
      isPullback :=
        S2058IsoWitness (h.baseChange T point).toSource
          (h.baseChange T point).projectionMap.transformation point e
          (h.baseChange T point).commutes
          ((S2058WhiskerLeftIso (h.baseChange T point).toSource p q e).symm.trans
            (h.baseChange T point).commutes)
          (h.baseChange T point).isPullback }
  hasProperty T point := h.hasProperty T point

/-- The finite-etale version: representable finite etaleness is invariant under
2-isomorphism of the stack morphism. -/
noncomputable def S2058IsoInvarianceFiniteEtale
    {X Z : EtaleStackOverField F} {p q : X.Hom Z} (e : Iso p q)
    (h : EtaleStackFiniteEtaleMorphism p) :
    EtaleStackFiniteEtaleMorphism q :=
  S2058IsoInvarianceProperty
    (fun f => AlgebraicGeometry.IsFinite f ∧ AlgebraicGeometry.Etale f) e h

/-! ## 4. Pasting of two two-pullback witnesses -/

/-- The data of a pasted pair of squares: a lower square P -> X over Ys and an
upper square Ys -> Zs over Y2. -/
structure S2058Pasting where
  P : EtaleStackPseudofunctor F
  X : EtaleStackPseudofunctor F
  Ys : EtaleStackPseudofunctor F
  Zs : EtaleStackPseudofunctor F
  Y2 : EtaleStackPseudofunctor F
  Z2 : EtaleStackPseudofunctor F
  toX1 : P ⟶ X
  toY1 : P ⟶ Ys
  x1 : X ⟶ Zs
  xi : Ys ⟶ Zs
  c1 : Iso (Pseudofunctor.StrongTrans.vcomp toX1 x1)
    (Pseudofunctor.StrongTrans.vcomp toY1 xi)
  toY2 : Ys ⟶ Y2
  x2 : Zs ⟶ Z2
  y2 : Y2 ⟶ Z2
  c2 : Iso (Pseudofunctor.StrongTrans.vcomp xi x2)
    (Pseudofunctor.StrongTrans.vcomp toY2 y2)
  gamma : Iso (Pseudofunctor.StrongTrans.vcomp toX1
    (Pseudofunctor.StrongTrans.vcomp x1 x2))
    (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp toY1 toY2) y2)

namespace S2058Pasting

/-- The lower square. -/
noncomputable def square1 (D : S2058Pasting (F := F)) :
    EtalePseudofunctorSquare D.P D.X D.Ys D.Zs :=
  EtalePseudofunctorSquare.mk D.toX1 D.toY1 D.x1 D.xi D.c1

/-- The upper square. -/
noncomputable def square2 (D : S2058Pasting (F := F)) :
    EtalePseudofunctorSquare D.Ys D.Zs D.Y2 D.Z2 :=
  EtalePseudofunctorSquare.mk D.xi D.toY2 D.x2 D.y2 D.c2

/-- The pasted square. -/
noncomputable def squareP (D : S2058Pasting (F := F)) :
    EtalePseudofunctorSquare D.P D.X D.Y2 D.Z2 :=
  EtalePseudofunctorSquare.mk D.toX1
    (Pseudofunctor.StrongTrans.vcomp D.toY1 D.toY2)
    (Pseudofunctor.StrongTrans.vcomp D.x1 D.x2) D.y2 D.gamma

/-- The cone of the upper square attached to a cone of the pasted square. -/
noncomputable def pastCone2 (D : S2058Pasting (F := F))
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    D.square2.Cone W where
  toX := Pseudofunctor.StrongTrans.vcomp cone.toX D.x1
  toY := cone.toY
  commutes := (S2058AssociatorIso cone.toX D.x1 D.x2).trans cone.commutes

theorem pastCone2_toX (D : S2058Pasting (F := F))
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastCone2 cone).toX = Pseudofunctor.StrongTrans.vcomp cone.toX D.x1 := rfl

theorem pastCone2_toY (D : S2058Pasting (F := F))
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastCone2 cone).toY = cone.toY := rfl

theorem pastCone2_commutes (D : S2058Pasting (F := F))
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastCone2 cone).commutes =
      (S2058AssociatorIso cone.toX D.x1 D.x2).trans cone.commutes := rfl

/-- The cone of the lower square attached to a cone of the pasted square. -/
noncomputable def pastCone1 (D : S2058Pasting (F := F))
    (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    D.square1.Cone W where
  toX := cone.toX
  toY := w2.lift W (D.pastCone2 cone)
  commutes := (w2.liftToX W (D.pastCone2 cone)).symm

/-- The lift of a cone of the pasted square. -/
noncomputable def pastLift (D : S2058Pasting (F := F))
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) : W ⟶ D.P :=
  w1.lift W (D.pastCone1 w2 cone)

/-- The comparison of the pasted lift with the first leg. -/
noncomputable def pastLiftToX (D : S2058Pasting (F := F))
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (D.pastLift w1 w2 cone) D.toX1) cone.toX :=
  w1.liftToX W (D.pastCone1 w2 cone)

/-- The comparison of the pasted lift with the second leg. -/
noncomputable def pastLiftToY (D : S2058Pasting (F := F))
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (D.pastLift w1 w2 cone)
      (Pseudofunctor.StrongTrans.vcomp D.toY1 D.toY2)) cone.toY :=
  (S2058AssociatorIso (D.pastLift w1 w2 cone) D.toY1 D.toY2).symm.trans
    ((S2058WhiskerRight (w1.liftToY W (D.pastCone1 w2 cone)) D.toY2).trans
      (w2.liftToY W (D.pastCone2 cone)))

end S2058Pasting

/-! ## 5. Composition of representable maps and the composite presentation -/

/-- Composition of two representable scheme maps: the composite strong
transformation and the composite scheme projection represent the composite
scheme morphism. -/
noncomputable def S2058SchemeRepresentableMapComp {S T U : SchemeOverField F}
    {f : S ⟶ T} {g : T ⟶ U}
    (Fm : SchemeRepresentableMap f) (Gm : SchemeRepresentableMap g) :
    SchemeRepresentableMap (f ≫ g) where
  transformation :=
    Pseudofunctor.StrongTrans.vcomp Fm.transformation Gm.transformation
  app_eq := by
    intro U'
    rw [show (Pseudofunctor.StrongTrans.vcomp Fm.transformation Gm.transformation).app
        (LocallyDiscrete.mk U') =
          Fm.transformation.app (LocallyDiscrete.mk U') ≫
            Gm.transformation.app (LocallyDiscrete.mk U') from
      Pseudofunctor.StrongTrans.comp_app _ _ _]
    rw [Fm.app_eq, Gm.app_eq]
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext
      (fun P => by
        apply Discrete.ext
        rfl)
      (by
        intro X Y h
        exact @Subsingleton.elim _
          (Discrete.instSubsingletonDiscreteHom _ _) _ _)

/-! ## 6. The exact missing bicategorical pasting statement -/

/-- **The exact missing bicategorical input**: the pasting of the two
two-pullback witnesses of two composable squares.  This is a pure bicategorical
coherence statement (no geometry).  The final hypothesis is automatic when the
apex of the pasted square is a representable stack (then every 2-cell type into
it is a subsingleton), which is the case in every base-change presentation. -/
def S2058PastingStatement : Type (u + 1) :=
  ∀ (D : S2058Pasting (F := F)),
    D.square1.TwoPullbackWitness → D.square2.TwoPullbackWitness →
      (∀ {W : EtaleStackPseudofunctor F} (a b : W ⟶ D.P), Subsingleton (a ⟶ b)) →
        D.squareP.TwoPullbackWitness

/-! ## 7. Composition closure of representable morphism properties -/

section Composition

variable {Xs Ys Zs : EtaleStackOverField F}

/-- The base-change presentation of a composite stack morphism, obtained by
pasting the presentations of the two morphisms.  The pullback scheme is the
apex of the first presentation, the projection is the composite of the two
scheme projections, and the comparison 2-isomorphism is the associator composite
of the two recorded comparisons. -/
noncomputable def S2058BaseChangeComp
    (P : forall {S T : Scheme.{u}}, (S ⟶ T) -> Prop)
    {p : Xs.Hom Ys} {q : Ys.Hom Zs}
    (hp : EtaleStackRepresentableMorphismProperty P p)
    (hq : EtaleStackRepresentableMorphismProperty P q)
    (hPcomp : forall {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U),
      P f -> P g -> P (f ≫ g))
    (T0 : SchemeOverField F)
    (pt0 : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F T0) Zs.fiber)
    (hsub : forall {T : SchemeOverField F} {W : EtaleStackPseudofunctor F}
      (a b : W ⟶ schemeRepresentableEtalePseudofunctor F T), Subsingleton (a ⟶ b))
    (hpast : S2058PastingStatement (F := F)) :
    EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp p q) T0 pt0 :=
  let bq := hq.baseChange T0 pt0
  let bp := hp.baseChange bq.pullbackScheme bq.toSource
  { pullbackScheme := bp.pullbackScheme
    projection := bp.projection ≫ bq.projection
    projectionMap := S2058SchemeRepresentableMapComp bp.projectionMap bq.projectionMap
    toSource := bp.toSource
    commutes :=
      (S2058AssociatorIso bp.toSource p q).symm.trans
        ((S2058WhiskerRight bp.commutes q).trans
          ((S2058AssociatorIso bp.projectionMap.transformation bq.toSource q).trans
            ((S2058WhiskerLeft bp.projectionMap.transformation bq.commutes).trans
              (S2058AssociatorIso bp.projectionMap.transformation
                bq.projectionMap.transformation pt0).symm)))
    isPullback :=
      hpast
        { P := (schemeRepresentableEtalePseudofunctor F bp.pullbackScheme)
          X := Xs.fiber
          Ys := schemeRepresentableEtalePseudofunctor F bq.pullbackScheme
          Zs := Ys.fiber
          Y2 := schemeRepresentableEtalePseudofunctor F T0
          Z2 := Zs.fiber
          toX1 := bp.toSource
          toY1 := bp.projectionMap.transformation
          x1 := p
          xi := bq.toSource
          c1 := bp.commutes
          toY2 := bq.projectionMap.transformation
          x2 := q
          y2 := pt0
          c2 := bq.commutes
          gamma :=
            (S2058AssociatorIso bp.toSource p q).symm.trans
              ((S2058WhiskerRight bp.commutes q).trans
                ((S2058AssociatorIso bp.projectionMap.transformation bq.toSource q).trans
                  ((S2058WhiskerLeft bp.projectionMap.transformation bq.commutes).trans
                    (S2058AssociatorIso bp.projectionMap.transformation
                      bq.projectionMap.transformation pt0).symm))) }
        bp.isPullback bq.isPullback
        (fun {W} a b => hsub a b) }

/-- **Composition closure** of a representable morphism property, modulo the
bicategorical pasting statement. -/
noncomputable def S2058CompositionClosureOfPasting
    (P : forall {S T : Scheme.{u}}, (S ⟶ T) -> Prop)
    (hpast : S2058PastingStatement (F := F))
    (hsub : forall {T : SchemeOverField F} {W : EtaleStackPseudofunctor F}
      (a b : W ⟶ schemeRepresentableEtalePseudofunctor F T), Subsingleton (a ⟶ b))
    (hPcomp : forall {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U),
      P f -> P g -> P (f ≫ g))
    {Xs Ys Zs : EtaleStackOverField F} {p : Xs.Hom Ys} {q : Ys.Hom Zs}
    (hp : EtaleStackRepresentableMorphismProperty P p)
    (hq : EtaleStackRepresentableMorphismProperty P q) :
    EtaleStackRepresentableMorphismProperty P
      (Pseudofunctor.StrongTrans.vcomp p q) where
  baseChange T0 pt0 :=
    S2058BaseChangeComp P hp hq hPcomp T0 pt0 hsub hpast
  hasProperty T0 pt0 :=
    hPcomp (hp.baseChange (hq.baseChange T0 pt0).pullbackScheme
        (hq.baseChange T0 pt0).toSource).projection.left
      (hq.baseChange T0 pt0).projection.left
      (hp.hasProperty (hq.baseChange T0 pt0).pullbackScheme
        (hq.baseChange T0 pt0).toSource)
      (hq.hasProperty T0 pt0)

end Composition

/-! ## 8. The exact missing 2-universal property of the iso-comma square -/

/-- The exact missing geometric input for the toA certificate: the sequence of
iso-comma projections of two actual cover maps is a bicategorical pullback with
the full 2-universal property, for *every* pseudo-cone over the cospan of cover
maps, not only for the bicones of an actual cover liftSite.  This is S1864 (d)
in its general form; the tree contains only the bicone case (and the fibre-level
universal property of S1893). -/
def S2058IsoCommaTwoPullback : Type 1 :=
  forall (A B C : LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper.S1728Cover)
    (f : LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper.S1728CoverMap A C)
    (g : LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper.S1728CoverMap B C),
    (EtalePseudofunctorSquare.mk
      (LeanFormal.IUT.XiFPaper.S1955AssembleCDActual.toA f g)
      (LeanFormal.IUT.XiFPaper.S1955AssembleCDActual.toB f g)
      f.map g.map (LeanFormal.IUT.XiFPaper.S1955AssembleCDActual.commutes f g)).TwoPullbackWitness

/-! ## 9. Paper-level reductions (D6(c)) -/

section Paper

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual

/-- S1892's 2-isomorphism transport statement for representable finite
etaleness (the third named input of S1892), proved. -/
theorem S2058TransportHolds :
    forall {W Z : EtaleStackOverField S1726K} {f g : W.Hom Z},
      Iso f g -> Nonempty (EtaleStackFiniteEtaleMorphism f) ->
        Nonempty (EtaleStackFiniteEtaleMorphism g) := by
  intro W Z f g e h
  exact ⟨S2058IsoInvarianceFiniteEtale e h.some⟩

/-- S2046's 2-isomorphism invariance statement, proved. -/
noncomputable def S2058IsoInvarianceStatement :
    forall {W Z : EtaleStackOverField S1726K} {f g : W.Hom Z},
      Iso f g -> EtaleStackFiniteEtaleMorphism f ->
        EtaleStackFiniteEtaleMorphism g := by
  intro W Z f g e h
  exact S2058IsoInvarianceFiniteEtale e h

/-- S2044's composition closure from the bicategorical pasting statement.  The
only remaining input is the pure bicategorical pasting S2058PastingStatement;
everything else (composite presentation, composed representable projection,
property closure) is constructed in section 7. -/
noncomputable def S2058S2044CompositionClosure_of_pasting
    (hpast : S2058PastingStatement (F := S1726K)) :
    S2044CompositionClosure := by
  intro X Y Z p q hp hq
  exact S2058CompositionClosureOfPasting
    (fun f => AlgebraicGeometry.IsFinite f ∧ AlgebraicGeometry.Etale f)
    hpast
    (fun {T} {W} a b =>
      LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual.S1897Modification_subsingleton_representable a b)
    (fun f g hf hg => by
      haveI := hf.1
      haveI := hf.2
      haveI := hg.1
      haveI := hg.2
      exact ⟨inferInstance, inferInstance⟩)
    hp hq

/-- D6(c) from the two named inputs.  Given the toA certificate and the
bicategorical pasting statement, the composite structure map of every cospan of
actual cover maps is representably finite etale. -/
noncomputable def S2058D6FiniteEtaleCertificate
    (hpast : S2058PastingStatement (F := S1726K))
    (htoA : S2044ToAFiniteEtaleField)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2044FiniteEtaleOfClosure (S2058S2044CompositionClosure_of_pasting hpast) htoA

end Paper

#print axioms S2058IsoWitness
#print axioms S2058IsoInvarianceProperty
#print axioms S2058IsoInvarianceFiniteEtale
#print axioms S2058SchemeRepresentableMapComp
#print axioms S2058BaseChangeComp
#print axioms S2058CompositionClosureOfPasting
#print axioms S2058S2044CompositionClosure_of_pasting
#print axioms S2058D6FiniteEtaleCertificate
#print axioms S2058TransportHolds
#print axioms S2058IsoInvarianceStatement

end LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual

end
