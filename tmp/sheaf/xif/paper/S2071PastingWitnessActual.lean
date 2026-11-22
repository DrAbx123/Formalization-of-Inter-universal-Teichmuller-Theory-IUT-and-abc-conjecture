import tmp.sheaf.xif.paper.S2066PastLiftToYComponentsActual

/-!
# S2071: the full pasted two-pullback witness (D6(c) pasting)

S2058 reduces D6(c) -- composition closure of representable finite etaleness --
to the pure bicategorical statement `S2058PastingStatement`: given the two
two-pullback witnesses of two composable squares, produce the full witness of
the pasted square.  S2064 built the corrected pasting datum and its first block
(lift, liftToX, liftToY); S2066 computed the explicit hom and inv 2-cells of
`pastLiftToY`.

This file completes the witness:

* `pastCone2Hom`: the morphism of cones over the second (upper) square induced
  by a morphism of cones over the pasted square.  Its compatibility is the
  associator coherence combined with the compatibility of the original cone
  morphism (`S2071ConeMorphismBottom`, proved from `whiskerRight_comp` and the
  associator laws, not from a new axiom).
* `pastCone1Hom`: the morphism of cones over the first (lower) square, whose
  `toY` component is `w2.liftTwoCell` applied to `pastCone2Hom`; compatibility
  uses `w2.liftTwoCell_toX` and the inverse laws of the two comparison
  isomorphisms (`S2071ConeMorphismTop`).
* `pastLiftTwoCell_toY`: the distribution of `liftTwoCell` along
  `toY1 ≫ toY2`.  This is exactly where the explicit `hom`/`inv` components of
  `pastLiftToY` computed in S2066 are used: `whiskerRight_comp` first splits the
  right whiskering, then `w1.liftTwoCell_toY` and `w2.liftTwoCell_toY` provide
  the two inner rectangles (`S2071LiftTwoCellToY`).
* `twoCell_ext` for the pasted square, unconditionally: joint faithfulness of
  the two projections of the pasted square follows from that of the two factor
  squares.  The one bicategorical input is `S2071WhiskerRight_base_iso`: right
  whiskering by two 2-isomorphic 1-cells is conjugated by left whiskerings of
  the 2-isomorphism (`whisker_exchange`), so faithfulness transfers across the
  pasting iso `c1`.
* `pastWitness` and `S2071PastingStatement_holds`: the statement is proved for
  every field `F`, hence the hypothesis `hsub` of `S2058PastingStatement`
  (subsingleton 2-cells at the apex, used by S2062/S2065) is not needed.

No sorry, no new axiom, no fabricated field.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2066PastLiftToYComponentsActual

universe u
variable {F : Type u} [Field F]

/-! ## 1. Bicategorical coherence lemmas used by the pasting

These are stated in an arbitrary bicategory; they are the standard associativity
coherences for a pasted square (no new axiom). -/

namespace Coherence

universe v w

variable {Bc : Type w} [Bicategory.{v, w} Bc]

/-- Compatibility of the cone morphism over the second (bottom) square of a
pasting. -/
theorem S2071ConeMorphismBottom {a b m l m' : Bc} {Us Ut : a ⟶ b} (nn : Us ⟶ Ut)
    {Vs Vt : a ⟶ l} (mq : Vs ⟶ Vt) (g : b ⟶ m) (bb : m ⟶ m') (y : l ⟶ m')
    (cs : Us ≫ (g ≫ bb) ≅ Vs ≫ y) (ct : Ut ≫ (g ≫ bb) ≅ Vt ≫ y)
    (hcomp : (nn ▷ (g ≫ bb)) ≫ ct.hom = cs.hom ≫ (mq ▷ y)) :
    ((nn ▷ g) ▷ bb) ≫ ((α_ Ut g bb).hom ≫ ct.hom) =
      ((α_ Us g bb).hom ≫ cs.hom) ≫ (mq ▷ y) := by
  have h1 : nn ▷ (g ≫ bb) = (α_ Us g bb).inv ≫ ((nn ▷ g) ▷ bb) ≫ (α_ Ut g bb).hom :=
    whiskerRight_comp nn g bb
  have h2 : ((α_ Us g bb).inv ≫ ((nn ▷ g) ▷ bb) ≫ (α_ Ut g bb).hom) ≫ ct.hom =
      cs.hom ≫ (mq ▷ y) := by
    rw [← h1]
    exact hcomp
  calc ((nn ▷ g) ▷ bb) ≫ ((α_ Ut g bb).hom ≫ ct.hom)
      = (α_ Us g bb).hom ≫
          (((α_ Us g bb).inv ≫ ((nn ▷ g) ▷ bb) ≫ (α_ Ut g bb).hom) ≫ ct.hom) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (α_ Us g bb).hom ≫ (cs.hom ≫ (mq ▷ y)) := by rw [h2]
    _ = ((α_ Us g bb).hom ≫ cs.hom) ≫ (mq ▷ y) := by rw [Category.assoc]

/-- Compatibility of the cone morphism over the first (top) square of a
pasting. -/
theorem S2071ConeMorphismTop {a b n m : Bc} {Us Ut : a ⟶ b} (nn : Us ⟶ Ut)
    {Vs Vt : a ⟶ n} (wc : Vs ⟶ Vt) (g : b ⟶ m) (y : n ⟶ m)
    (Bs : Vs ≫ y ≅ Us ≫ g) (Bt : Vt ≫ y ≅ Ut ≫ g)
    (hyp : wc ▷ y = Bs.hom ≫ (nn ▷ g) ≫ Bt.inv) :
    (nn ▷ g) ≫ Bt.inv = Bs.inv ≫ (wc ▷ y) := by
  rw [hyp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Distribution of a 2-cell over the pasted second leg: the explicit form of
`liftTwoCell_toY` for a pasted square.  `h1` is the first square's
`liftTwoCell_toY`, `h2` the second square's. -/
theorem S2071LiftTwoCellToY {a p n l : Bc} {Ls Lt : a ⟶ p} (wtc : Ls ⟶ Lt)
    (tY : p ⟶ n) (bY : n ⟶ l)
    {Vs Vt : a ⟶ l} (mq : Vs ⟶ Vt)
    {Dbs Dbt : a ⟶ n} (wbc : Dbs ⟶ Dbt)
    (Cs : Ls ≫ tY ≅ Dbs) (Ct : Lt ≫ tY ≅ Dbt)
    (Ds : Dbs ≫ bY ≅ Vs) (Dt : Dbt ≫ bY ≅ Vt)
    (h1 : wtc ▷ tY = Cs.hom ≫ wbc ≫ Ct.inv)
    (h2 : wbc ▷ bY = Ds.hom ≫ mq ≫ Dt.inv) :
    wtc ▷ (tY ≫ bY) =
      ((α_ Ls tY bY).inv ≫ (Cs.hom ▷ bY) ≫ Ds.hom) ≫ mq ≫
        (Dt.inv ≫ (Ct.inv ▷ bY) ≫ (α_ Lt tY bY).hom) := by
  have hw : wtc ▷ (tY ≫ bY) = (α_ Ls tY bY).inv ≫ ((wtc ▷ tY) ▷ bY) ≫ (α_ Lt tY bY).hom :=
    whiskerRight_comp wtc tY bY
  rw [hw, h1]
  simp only [comp_whiskerRight]
  rw [h2]
  simp only [Category.assoc]

/-! ### Transport of right whiskering along a 2-isomorphism -/

/-- Right whiskering of a 2-cell by two 2-isomorphic 1-cells: the two composites
are conjugated by left whiskerings of the 2-isomorphism. -/
theorem S2071WhiskerRight_base_iso_formula {a b c : Bc} {f g : a ⟶ b} (al : f ⟶ g)
    {u u' : b ⟶ c} (e : u ≅ u') :
    al ▷ u' = (f ◁ e.inv) ≫ (al ▷ u) ≫ (g ◁ e.hom) := by
  calc al ▷ u'
      = ((f ◁ e.inv) ≫ (f ◁ e.hom)) ≫ al ▷ u' := by
        rw [whiskerLeft_inv_hom, Category.id_comp]
    _ = (f ◁ e.inv) ≫ ((f ◁ e.hom) ≫ al ▷ u') := by rw [Category.assoc]
    _ = (f ◁ e.inv) ≫ (al ▷ u ≫ (g ◁ e.hom)) := by rw [whisker_exchange]
    _ = (f ◁ e.inv) ≫ (al ▷ u) ≫ (g ◁ e.hom) := rfl

/-- Equality of right whiskerings transfers across a 2-isomorphism of the
whiskering 1-cell. -/
theorem S2071WhiskerRight_base_iso {a b c : Bc} {f g : a ⟶ b} {al be : f ⟶ g}
    {u u' : b ⟶ c} (e : u ≅ u') (h : al ▷ u = be ▷ u) : al ▷ u' = be ▷ u' := by
  rw [S2071WhiskerRight_base_iso_formula al e, S2071WhiskerRight_base_iso_formula be e, h]

/-- Equality of right whiskerings propagates to the composite 1-cell. -/
theorem S2071WhiskerRight_comp_congr {a b c d : Bc} {f g : a ⟶ b} {al be : f ⟶ g}
    {u : b ⟶ c} (h : al ▷ u = be ▷ u) (v : c ⟶ d) :
    al ▷ (u ≫ v) = be ▷ (u ≫ v) := by
  rw [whiskerRight_comp, whiskerRight_comp, h]

/-- Equality of right whiskerings of a composite splits off the second factor. -/
theorem S2071WhiskerRight_comp_congr' {a b c d : Bc} {f g : a ⟶ b} {al be : f ⟶ g}
    {u : b ⟶ c} (v : c ⟶ d) (h : al ▷ (u ≫ v) = be ▷ (u ≫ v)) :
    (al ▷ u) ▷ v = (be ▷ u) ▷ v := by
  rw [whiskerRight_comp, whiskerRight_comp] at h
  have h1 : (al ▷ u) ▷ v ≫ (α_ g u v).hom = (be ▷ u) ▷ v ≫ (α_ g u v).hom := by
    have hh := congrArg (fun t => (α_ f u v).hom ≫ t) h
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hh
  have h2 := congrArg (fun t => t ≫ (α_ g u v).inv) h1
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h2

end Coherence

/-! ## 2. Cone morphisms over the two factor squares -/

section Pasting

variable (D : S2058Pasting (F := F))

/-- The morphism of cones over the second (upper) square induced by a morphism
of cones over the pasted square. -/
noncomputable def pastCone2Hom (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} {s t : D.squareP.Cone W}
    (m : D.squareP.ConeMorphism s t) :
    D.square2.ConeMorphism (D.pastCone2 s) (D.pastCone2 t) where
  toX := Bicategory.whiskerRight m.toX D.x1
  toY := m.toY
  compatibility := by
    have hs : (D.pastCone2 s).commutes.hom =
        (Bicategory.associator s.toX D.x1 D.x2).hom ≫ s.commutes.hom := rfl
    have ht : (D.pastCone2 t).commutes.hom =
        (Bicategory.associator t.toX D.x1 D.x2).hom ≫ t.commutes.hom := rfl
    rw [hs, ht]
    exact Coherence.S2071ConeMorphismBottom (Bc := EtaleStackPseudofunctor F)
      m.toX m.toY D.x1 D.x2 D.y2 s.commutes t.commutes m.compatibility

/-- The morphism of cones over the first (lower) square induced by a morphism
of cones over the pasted square. -/
noncomputable def pastCone1Hom (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} {s t : D.squareP.Cone W}
    (m : D.squareP.ConeMorphism s t) :
    D.square1.ConeMorphism (D.pastCone1 w2 s) (D.pastCone1 w2 t) where
  toX := m.toX
  toY := w2.liftTwoCell W (D.pastCone2 s) (D.pastCone2 t) (pastCone2Hom D w2 m)
  compatibility := by
    have hs : (D.pastCone1 w2 s).commutes.hom = (w2.liftToX W (D.pastCone2 s)).inv := rfl
    have ht : (D.pastCone1 w2 t).commutes.hom = (w2.liftToX W (D.pastCone2 t)).inv := rfl
    rw [hs, ht]
    exact Coherence.S2071ConeMorphismTop (Bc := EtaleStackPseudofunctor F)
      m.toX
      (w2.liftTwoCell W (D.pastCone2 s) (D.pastCone2 t) (pastCone2Hom D w2 m))
      D.x1 D.xi
      (w2.liftToX W (D.pastCone2 s)) (w2.liftToX W (D.pastCone2 t))
      (w2.liftTwoCell_toX W (D.pastCone2 s) (D.pastCone2 t) (pastCone2Hom D w2 m))

/-! ## 3. `liftTwoCell` and its two projection equations -/

/-- The `liftTwoCell` field of the pasted witness. -/
noncomputable def pastLiftTwoCell
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} {s t : D.squareP.Cone W}
    (m : D.squareP.ConeMorphism s t) :
    D.pastLift w1 w2 s ⟶ D.pastLift w1 w2 t :=
  w1.liftTwoCell W (D.pastCone1 w2 s) (D.pastCone1 w2 t) (pastCone1Hom D w2 m)

/-- The first projection equation of the pasted `liftTwoCell`; it is exactly
`w1.liftTwoCell_toX` because the first legs of the pasted square and of the
first square agree. -/
theorem pastLiftTwoCell_toX
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} {s t : D.squareP.Cone W}
    (m : D.squareP.ConeMorphism s t) :
    Bicategory.whiskerRight (pastLiftTwoCell D w1 w2 m) D.squareP.toX =
      (D.pastLiftToX w1 w2 s).hom ≫ m.toX ≫ (D.pastLiftToX w1 w2 t).inv :=
  w1.liftTwoCell_toX W (D.pastCone1 w2 s) (D.pastCone1 w2 t) (pastCone1Hom D w2 m)

/-- The second projection equation of the pasted `liftTwoCell`: distribution
along `toY1 ≫ toY2`, with the explicit components of `pastLiftToY` from
S2066 on both ends. -/
theorem pastLiftTwoCell_toY
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} {s t : D.squareP.Cone W}
    (m : D.squareP.ConeMorphism s t) :
    Bicategory.whiskerRight (pastLiftTwoCell D w1 w2 m) D.squareP.toY =
      (D.pastLiftToY w1 w2 s).hom ≫ m.toY ≫ (D.pastLiftToY w1 w2 t).inv := by
  rw [S2066_pastLiftToY_hom w1 w2 s, S2066_pastLiftToY_inv w1 w2 t]
  exact Coherence.S2071LiftTwoCellToY (Bc := EtaleStackPseudofunctor F)
    (wtc := pastLiftTwoCell D w1 w2 m) (tY := D.toY1) (bY := D.toY2) (mq := m.toY)
    (wbc := w2.liftTwoCell W (D.pastCone2 s) (D.pastCone2 t) (pastCone2Hom D w2 m))
    (Cs := w1.liftToY W (D.pastCone1 w2 s)) (Ct := w1.liftToY W (D.pastCone1 w2 t))
    (Ds := w2.liftToY W (D.pastCone2 s)) (Dt := w2.liftToY W (D.pastCone2 t))
    (h1 := w1.liftTwoCell_toY W (D.pastCone1 w2 s) (D.pastCone1 w2 t) (pastCone1Hom D w2 m))
    (h2 := w2.liftTwoCell_toY W (D.pastCone2 s) (D.pastCone2 t) (pastCone2Hom D w2 m))

/-! ## 4. `twoCell_ext` of the pasted square -/

/-- Joint faithfulness of the two projections of the pasted square, derived from
that of the two factor squares.  The pasting iso `D.c1` conjugates the two
whiskerings, which makes up for the fact that right whiskering by `D.toY2`
alone is not faithful. -/
theorem pastTwoCell_ext
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F}
    {first second : Pseudofunctor.StrongTrans W D.P} (alpha beta : first ⟶ second)
    (h1 : Bicategory.whiskerRight alpha D.toX1 = Bicategory.whiskerRight beta D.toX1)
    (h2 : Bicategory.whiskerRight alpha (D.toY1 ≫ D.toY2) =
      Bicategory.whiskerRight beta (D.toY1 ≫ D.toY2)) :
    alpha = beta := by
  have hx' := Coherence.S2071WhiskerRight_comp_congr
    (Bc := EtaleStackPseudofunctor F) h1 D.x1
  have hy' := Coherence.S2071WhiskerRight_base_iso (Bc := EtaleStackPseudofunctor F) D.c1 hx'
  have hxi := Coherence.S2071WhiskerRight_comp_congr'
    (Bc := EtaleStackPseudofunctor F) D.xi hy'
  have htoY2 := Coherence.S2071WhiskerRight_comp_congr'
    (Bc := EtaleStackPseudofunctor F) D.toY2 h2
  have hY1 : Bicategory.whiskerRight alpha D.toY1 =
      Bicategory.whiskerRight beta D.toY1 :=
    w2.twoCell_ext W (first := first ≫ D.toY1) (second := second ≫ D.toY1)
      (alpha ▷ D.toY1) (beta ▷ D.toY1) hxi htoY2
  exact w1.twoCell_ext W (first := first) (second := second) alpha beta h1 hY1

/-! ## 5. The witness and the statement -/

/-- The full two-pullback witness of the pasted square. -/
noncomputable def pastWitness
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness) :
    D.squareP.TwoPullbackWitness where
  lift W cone := D.pastLift w1 w2 cone
  liftToX W cone := D.pastLiftToX w1 w2 cone
  liftToY W cone := D.pastLiftToY w1 w2 cone
  liftTwoCell W s t m := pastLiftTwoCell D w1 w2 m
  liftTwoCell_toX W s t m := pastLiftTwoCell_toX D w1 w2 m
  liftTwoCell_toY W s t m := pastLiftTwoCell_toY D w1 w2 m
  twoCell_ext W first second alpha beta h1 h2 := pastTwoCell_ext D w1 w2 alpha beta h1 h2

/-- **D6(c) pasting**: the exact missing bicategorical input of S2058 is proved
for every field.  The subsingleton hypothesis carried by
`S2058PastingStatement` is not needed: `twoCell_ext` is derived from the two
factor witnesses. -/
noncomputable def S2071PastingStatement_holds :
    S2058PastingStatement (F := F) :=
  fun D w1 w2 _hsub => pastWitness D w1 w2

/-! ## 6. The D6(c) consumer: S2044 composition closure, unconditional -/

section Paper

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual

/-- S2044's composition closure of representable finite etaleness, with the
pasting hypothesis supplied by `S2071PastingStatement_holds`. -/
noncomputable def S2071S2044CompositionClosure : S2044CompositionClosure :=
  S2058S2044CompositionClosure_of_pasting (S2071PastingStatement_holds (F := S1726K))

end Paper

/-! ## 7. Checks and axiom audit -/

#check @pastCone2Hom
#check @pastCone1Hom
#check @pastLiftTwoCell
#check @pastLiftTwoCell_toX
#check @pastLiftTwoCell_toY
#check @pastTwoCell_ext
#check @pastWitness
#check @S2071PastingStatement_holds

#print axioms pastCone2Hom
#print axioms pastCone1Hom
#print axioms pastLiftTwoCell_toX
#print axioms pastLiftTwoCell_toY
#print axioms pastTwoCell_ext
#print axioms pastWitness
#print axioms S2071PastingStatement_holds
#print axioms S2071S2044CompositionClosure

end Pasting

end LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual

end
