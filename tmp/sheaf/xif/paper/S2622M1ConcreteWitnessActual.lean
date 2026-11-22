/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2622
-/
import tmp.sheaf.xif.paper.S2620M1CoherenceFields

/-!
# S2622: an actual `M1RightCancellationWitness` for `y = 𝟙`

`S2620M1CoherenceFields.M1RightCancellationWitness y` is the coherence demanded
by the M1 cancellation step of S2618/S2619/S2620: from a base-change
presentation `Qx` of the composite `m ≫ y` at the composite point
`ptY ≫ y`, together with a commutation `commutes` of the `m`-square, one must
produce the full two-pullback witness of that `m`-square.

The key observation is that a `TwoPullbackWitness` is invariant under replacing
**both** base legs of the square by 2-isomorphic ones, as long as the two
top-left legs (`toX`, `toY`) are kept fixed.  The reason is that the apex
`P` and the legs `toX`, `toY` are untouched, so the transferred lift, the
two comparison isomorphisms and the two `_toX`/`_toY` coherence equations are
already of the required form; only the action on cone morphisms has to be
precomposed with the (identity-on-legs) comparison of cones, and its
compatibility is one `Bicategory.whisker_exchange`.  This is proved in
`S2622IsoWitness` below (a two-leg version of `S2058IsoWitness`).

The identity morphism is the concrete case in which the required 2-isomorphisms
exist without extra data: they are the right unitors
`(m ≫ 𝟙) ≅ m` and `(ptY ≫ 𝟙) ≅ ptY`.  Hence
`m1RightCancellationWitnessId` is an unconditional inhabitant of
`M1RightCancellationWitness (𝟙 Y)` for every etale stack `Y` over
`S1726K`, and `rightCancellationId` likewise inhabits the S2619 interface
`RightCancellation (𝟙 Y)`.  As a consumer we construct, for `y = 𝟙`, the
base-change presentation of `m` at `ptY` from a presentation of `m ≫ 𝟙`
at `ptY ≫ 𝟙` (`presentationOfId`), and we record the concrete instance at the
actual S1726 orbicurve stack.

## Honest boundary

* No `sorry`, no new axiom, no `Shrink`/`PUnit`, no fabricated 2-cell: the
  only inputs are the given presentation `Qx`, its two-pullback witness, and
  the right unitors of the pseudofunctor bicategory.
* The case `y = S1742StrongTransOfHom s` (the 2-Yoneda strong transformation
  of a scheme morphism `s`) is **not** obtained here.  The transport above needs
  2-isomorphisms `m ≫ y ≅ m` and `ptY ≫ y ≅ ptY`, which exist for the
  identity but not for a general `y`; that case is precisely the genuine right
  cancellation content of S2619/S2621 and remains open.  (The concrete identity
  witness `S2514IdentityFiniteEtaleActual.S2514IdWitness` lives over the field
  `S2480QiActual.F` and the base-change witnesses of
  `S2512StackOpenImmersionUB` live over `UB`, while
  `M1RightCancellationWitness` is stated over `S1726K`; the identity
  statement proved here is field-independent in form and covers the `S1726K`
  instance consumed by M1.)
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2618M1CancellationGoal
open LeanFormal.IUT.XiFPaper.S2619RightCancellationActual
open LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields

namespace LeanFormal.IUT.XiFPaper.S2622M1ConcreteWitnessActual

universe u

/-! ## 1. Two-pullback witnesses are invariant under 2-isomorphisms of both legs -/

section Transport

variable {F : Type u} [Field F]

/-- The cone of the square with base legs `x` and `xi` attached to a cone of
the square with the 2-isomorphic base legs `x'` and `xi'`.  The two top-left
legs are unchanged; the two commutations are composed with the whiskered
2-isomorphisms. -/
noncomputable def S2622OldCone {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y)
    {x x' : X ⟶ Z} (eX : Iso x x')
    {xi xi' : Y ⟶ Z} (eY : Iso xi xi')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi'))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi' c').Cone W) :
    (EtalePseudofunctorSquare.mk toX toY x xi c).Cone W where
  toX := cone.toX
  toY := cone.toY
  commutes := (S2058WhiskerLeftIso cone.toX x x' eX).trans
    (cone.commutes.trans (S2058WhiskerLeftIso cone.toY xi' xi eY.symm))

theorem S2622OldCone_toX {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y)
    {x x' : X ⟶ Z} (eX : Iso x x')
    {xi xi' : Y ⟶ Z} (eY : Iso xi xi')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi'))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi' c').Cone W) :
    (S2622OldCone toX toY eX eY c c' cone).toX = cone.toX := rfl

theorem S2622OldCone_toY {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y)
    {x x' : X ⟶ Z} (eX : Iso x x')
    {xi xi' : Y ⟶ Z} (eY : Iso xi xi')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi'))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi' c').Cone W) :
    (S2622OldCone toX toY eX eY c c' cone).toY = cone.toY := rfl

theorem S2622OldCone_commutes {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y)
    {x x' : X ⟶ Z} (eX : Iso x x')
    {xi xi' : Y ⟶ Z} (eY : Iso xi xi')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi'))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi' c').Cone W) :
    (S2622OldCone toX toY eX eY c c' cone).commutes =
      (S2058WhiskerLeftIso cone.toX x x' eX).trans
        (cone.commutes.trans (S2058WhiskerLeftIso cone.toY xi' xi eY.symm)) := rfl

/-- The commutation of the transported cone, on underlying 2-cells. -/
theorem S2622OldCone_commutes_hom {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y)
    {x x' : X ⟶ Z} (eX : Iso x x')
    {xi xi' : Y ⟶ Z} (eY : Iso xi xi')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi'))
    {W : EtaleStackPseudofunctor F}
    (cone : (EtalePseudofunctorSquare.mk toX toY x' xi' c').Cone W) :
    (S2622OldCone toX toY eX eY c c' cone).commutes.hom =
      (cone.toX ◁ eX.hom) ≫ (cone.commutes.hom ≫ (cone.toY ◁ eY.inv)) := rfl

/-- A morphism of cones of the square with base legs `x'`, `xi'` induces a
morphism of the corresponding transported cones of the square with legs `x`,
`xi`.  Its compatibility is the exchange law together with the cone morphism's
own compatibility. -/
noncomputable def S2622OldHom {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y)
    {x x' : X ⟶ Z} (eX : Iso x x')
    {xi xi' : Y ⟶ Z} (eY : Iso xi xi')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi'))
    {W : EtaleStackPseudofunctor F}
    {s t : (EtalePseudofunctorSquare.mk toX toY x' xi' c').Cone W}
    (m : (EtalePseudofunctorSquare.mk toX toY x' xi' c').ConeMorphism s t) :
    (EtalePseudofunctorSquare.mk toX toY x xi c).ConeMorphism
      (S2622OldCone toX toY eX eY c c' s)
      (S2622OldCone toX toY eX eY c c' t) where
  toX := m.toX
  toY := m.toY
  compatibility := by
    rw [S2622OldCone_commutes_hom, S2622OldCone_commutes_hom]
    have hsq : ((m.toX) ▷ x) ≫ (t.toX ◁ eX.hom) =
        (s.toX ◁ eX.hom) ≫ ((m.toX) ▷ x') := by
      rw [Bicategory.whisker_exchange]
    have hsq2 : ((m.toY) ▷ xi') ≫ (t.toY ◁ eY.inv) =
        (s.toY ◁ eY.inv) ≫ ((m.toY) ▷ xi) := by
      rw [Bicategory.whisker_exchange]
    have hcompat : ((m.toX) ▷ x') ≫ t.commutes.hom =
        s.commutes.hom ≫ ((m.toY) ▷ xi') := m.compatibility
    calc
      ((m.toX) ▷ x) ≫ ((t.toX ◁ eX.hom) ≫ (t.commutes.hom ≫ (t.toY ◁ eY.inv)))
          = (((m.toX) ▷ x) ≫ (t.toX ◁ eX.hom)) ≫
              (t.commutes.hom ≫ (t.toY ◁ eY.inv)) := by
            simp only [Category.assoc]
      _ = ((s.toX ◁ eX.hom) ≫ ((m.toX) ▷ x')) ≫
              (t.commutes.hom ≫ (t.toY ◁ eY.inv)) := by
            rw [hsq]
      _ = (s.toX ◁ eX.hom) ≫
              ((((m.toX) ▷ x') ≫ t.commutes.hom) ≫ (t.toY ◁ eY.inv)) := by
            simp only [Category.assoc]
      _ = (s.toX ◁ eX.hom) ≫
              ((s.commutes.hom ≫ ((m.toY) ▷ xi')) ≫ (t.toY ◁ eY.inv)) := by
            rw [hcompat]
      _ = (s.toX ◁ eX.hom) ≫
              (s.commutes.hom ≫ (((m.toY) ▷ xi') ≫ (t.toY ◁ eY.inv))) := by
            simp only [Category.assoc]
      _ = (s.toX ◁ eX.hom) ≫
              (s.commutes.hom ≫ ((s.toY ◁ eY.inv) ≫ ((m.toY) ▷ xi))) := by
            rw [hsq2]
      _ = (((s.toX ◁ eX.hom) ≫ (s.commutes.hom ≫ (s.toY ◁ eY.inv))) ≫
              ((m.toY) ▷ xi)) := by
            simp only [Category.assoc]

/-- **S2622**: 2-isomorphism invariance of the two-pullback witness in both base
legs.  If the square with base legs `x`, `xi` is a bicategorical pullback, so
is the square with the 2-isomorphic base legs `x'`, `xi'`, for any
commutations `c`, `c'`.  The apex and the two legs `toX`, `toY` are
unchanged. -/
noncomputable def S2622IsoWitness {P X Y Z : EtaleStackPseudofunctor F}
    (toX : P ⟶ X) (toY : P ⟶ Y)
    {x x' : X ⟶ Z} (eX : Iso x x')
    {xi xi' : Y ⟶ Z} (eY : Iso xi xi')
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY xi))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x')
      (Pseudofunctor.StrongTrans.vcomp toY xi'))
    (w : (EtalePseudofunctorSquare.mk toX toY x xi c).TwoPullbackWitness) :
    (EtalePseudofunctorSquare.mk toX toY x' xi' c').TwoPullbackWitness where
  lift W cone := w.lift W (S2622OldCone toX toY eX eY c c' cone)
  liftToX W cone := w.liftToX W (S2622OldCone toX toY eX eY c c' cone)
  liftToY W cone := w.liftToY W (S2622OldCone toX toY eX eY c c' cone)
  liftTwoCell W s t m :=
    w.liftTwoCell W (S2622OldCone toX toY eX eY c c' s)
      (S2622OldCone toX toY eX eY c c' t) (S2622OldHom toX toY eX eY c c' m)
  liftTwoCell_toX W s t m :=
    w.liftTwoCell_toX W (S2622OldCone toX toY eX eY c c' s)
      (S2622OldCone toX toY eX eY c c' t) (S2622OldHom toX toY eX eY c c' m)
  liftTwoCell_toY W s t m :=
    w.liftTwoCell_toY W (S2622OldCone toX toY eX eY c c' s)
      (S2622OldCone toX toY eX eY c c' t) (S2622OldHom toX toY eX eY c c' m)
  twoCell_ext W first second alpha beta h1 h2 :=
    w.twoCell_ext W (first := first) (second := second) alpha beta h1 h2

end Transport

/-! ## 2. The witness for the identity morphism -/

section Identity

variable {Y : EtaleStackOverField S1726K}

/-- **S2622**: from a base-change presentation of `m ≫ 𝟙` at `ptY ≫ 𝟙`, a
commutation of the `m`-square, and the presentation's two-pullback witness, we
obtain the two-pullback witness of the `m`-square itself. -/
noncomputable def cancelWitnessId {X : EtaleStackOverField S1726K} (m : X.Hom Y)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m (Pseudofunctor.StrongTrans.id Y.fiber)) T
      (Pseudofunctor.StrongTrans.vcomp ptY (Pseudofunctor.StrongTrans.id Y.fiber)))
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
      (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY)) :
    (EtalePseudofunctorSquare.mk
      Qx.toSource Qx.projectionMap.transformation m ptY commutes).TwoPullbackWitness :=
  S2622IsoWitness (toX := Qx.toSource) (toY := Qx.projectionMap.transformation)
    (eX := Pseudofunctor.StrongTrans.rightUnitor m)
    (eY := Pseudofunctor.StrongTrans.rightUnitor ptY)
    (c := Qx.commutes) (c' := commutes) Qx.isPullback

/-- **S2622**: the actual right-cancellation witness for the identity morphism
of an etale stack over `S1726K`; this is the concrete case of the M1 coherence
`M1RightCancellationWitness`. -/
noncomputable def m1RightCancellationWitnessId (Y : EtaleStackOverField S1726K) :
    M1RightCancellationWitness (Y := Y) (Z := Y)
      (Pseudofunctor.StrongTrans.id Y.fiber) :=
  { cancelWitness := fun {X} m T ptY Qx commutes =>
      cancelWitnessId (Y := Y) m T ptY Qx commutes }

/-- **S2622**: the same unitors yield the S2619 cancellation interface at the
identity morphism: whiskering by `𝟙` is conservative on 2-isomorphisms. -/
noncomputable def rightCancellationId (Y : EtaleStackOverField S1726K) :
    RightCancellation (Y := Y) (Z := Y)
      (Pseudofunctor.StrongTrans.id Y.fiber) :=
  { cancelRight := fun {P} A B e =>
      ((Pseudofunctor.StrongTrans.rightUnitor A).symm).trans
        (e.trans (Pseudofunctor.StrongTrans.rightUnitor B)) }

/-- The concrete instance at the actual S1726 orbicurve stack. -/
noncomputable def m1RightCancellationWitnessS1726Orbicurve :
    M1RightCancellationWitness (Y := S1726Orbicurve.stack)
      (Z := S1726Orbicurve.stack)
      (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber) :=
  m1RightCancellationWitnessId S1726Orbicurve.stack

end Identity

/-! ## 3. Consumer: the base-change presentation of `m` at `ptY` when `y = 𝟙` -/

section Consumer

/-- **S2622**: with the identity witness, a presentation of `m ≫ 𝟙` at
`ptY ≫ 𝟙` yields an actual base-change presentation of `m` at `ptY`, with
the same apex and the same scheme projection.  This is the `y = 𝟙` case of the
corrected consumer `BaseChangePresentationFieldWithHypotheses` of S2620. -/
noncomputable def presentationOfId {X Y : EtaleStackOverField S1726K}
    (m : X.Hom Y) (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m (Pseudofunctor.StrongTrans.id Y.fiber)) T
      (Pseudofunctor.StrongTrans.vcomp ptY (Pseudofunctor.StrongTrans.id Y.fiber))) :
    EtaleStackBaseChangePresentation m T ptY :=
  let commutes :=
    cancellationOf m (Pseudofunctor.StrongTrans.id Y.fiber)
      (rightCancellationId Y) T ptY Qx
  { pullbackScheme := Qx.pullbackScheme
    projection := Qx.projection
    projectionMap := Qx.projectionMap
    toSource := Qx.toSource
    commutes := commutes
    isPullback :=
      (m1RightCancellationWitnessId Y).cancelWitness (X := X) m T ptY Qx commutes }

end Consumer

/-! ## 4. Target-locked type checks -/

example (Y : EtaleStackOverField S1726K) :
    M1RightCancellationWitness (Y := Y) (Z := Y)
      (Pseudofunctor.StrongTrans.id Y.fiber) :=
  m1RightCancellationWitnessId Y

example (Y : EtaleStackOverField S1726K) :
    RightCancellation (Y := Y) (Z := Y)
      (Pseudofunctor.StrongTrans.id Y.fiber) :=
  rightCancellationId Y

example : M1RightCancellationWitness (Y := S1726Orbicurve.stack)
      (Z := S1726Orbicurve.stack)
      (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber) :=
  m1RightCancellationWitnessS1726Orbicurve

/-! ## 5. Axiom audit -/

#print axioms S2622OldCone
#print axioms S2622OldHom
#print axioms S2622IsoWitness
#print axioms cancelWitnessId
#print axioms m1RightCancellationWitnessId
#print axioms rightCancellationId
#print axioms m1RightCancellationWitnessS1726Orbicurve
#print axioms presentationOfId

end LeanFormal.IUT.XiFPaper.S2622M1ConcreteWitnessActual
end
