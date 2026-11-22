import tmp.sheaf.xif.paper.S2097BaseChangeButterflyActual

/-!
# S2108: the pasted-square transport of the S2097 butterfly reduction

## The target

`S2097TwoFullInputs.pastedTransport` was stated in S2097 as a *field*: for every
cospan `f : A ⟶ C`, `g : B ⟶ C`, test point `ptA : h_T ⟶ A` and `g`-base-change
presentation `Pg`, the full cone essential-surjectivity `S1852ConeEssSurj Pg` of
the presentation's square should give the weak two-pullback witness and the full
cone essential-surjectivity of the *pasted* square

  pullbackScheme --S2086Lift--> A ×_C B
        |                            |
  projectionMap                     toA
        v                            v
        T -----------ptA-----------> A

This file constructs that transport.  The only remaining input of the
butterfly theorem is then the genuine 2-categorical right-cancellation lemma
`S2097RightCancelStatement` of S2097; nothing else is assumed.

## What is proved here

* `S2108LiftTwoCellToY`: the bicategorical coherence used by the transport of
  `liftTwoCell_toY`.  Right whiskering of a 2-cell by two 2-isomorphic 1-cells is
  conjugated by left whiskerings of the 2-isomorphism
  (`Bicategory.whisker_exchange`); this is the only coherence needed, and it is
  already available as `S2071WhiskerRight_base_iso_formula`.
* `S2108IsoWitnessY`: replacing the *leg out of the apex* `toY` of a square by a
  2-isomorphic leg `toY'` transports the recorded `TwoPullbackWitness`, for an
  **arbitrary** new comparison 2-cell `c'`.  No coherence between `c` and `c'` is
  needed: the cones of the two squares are the same data, only `liftToY` changes
  by the whiskered 2-isomorphism.
* `S2108EssSurjY`: the same transport for the full cone essential-surjectivity
  `S1827EssSurjOf`.
* `S2108SwapEssSurj`: the base-pair swap `S2097SwapWitness` preserves the full
  cone essential-surjectivity (S2097 recorded the swap only for the weak
  witness).
* `S2108PastedWitness`, `S2108PastedFull`, `S2108PastedSquareFull`: the
  transport of `Pg.isPullback` and `S1852ConeEssSurj Pg` along the explicit
  square isomorphism.  The square of `Pg` is first swapped (the base pair
  `(g.map, ptA ; f.map)` becomes `(ptA ; f.map, g.map)`, exactly the base pair of
  the pasted square), then its first leg `Pg.toSource` is replaced by
  `S2086Lift ; toB` along `S2097LiftToB`, and the comparison 2-cell is replaced
  by `S2097Pasting`'s `gamma`.
* `S2108PastedTransport`: the function implementing the `pastedTransport` field,
  and `S2108TwoFullInputs`: `S2097TwoFullInputs` built from the two S2094 inputs
  alone.
* `S2108BaseChangePullback_of_rightCancel`: **the butterfly theorem with only
  `S2097RightCancelStatement` missing**.

## Honest boundary

No `sorry`, no new axiom, no change of any recorded definition.  Every field is
constructed from the recorded data; the only bicategorical input is the
`whisker_exchange` coherence already used by S2071.  The axiom footprint is the
same as S2097's (`propext`, `Classical.choice`, `Quot.sound`).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2108PastedTransportActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual
open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual.Coherence
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual

universe u

/-! ## 1. The one bicategorical coherence of the transport

Right whiskering of a 2-cell `m'` by the two 2-isomorphic 1-cells `u` and `u'`
is conjugated by left whiskerings of the 2-isomorphism `e : u ≅ u'`.  This is
`Bicategory.whisker_exchange`, packaged in S2071. -/

section CoherenceLeg

universe v w

variable {Bc : Type w} [Bicategory.{v, w} Bc]

/-- The `liftTwoCell_toY` coherence of the leg transport: if `m'` distributes
over the leg `u` through the comparison isomorphisms `hs` and `ht`, then it
distributes over the 2-isomorphic leg `u'` through the same comparisons composed
with the left whiskerings of `e`. -/
theorem S2108LiftTwoCellToY {a b c : Bc} {Ls Lt : a ⟶ b} (m' : Ls ⟶ Lt)
    {u u' : b ⟶ c} (e : u ≅ u')
    {Vs Vt : a ⟶ c} (mq : Vs ⟶ Vt)
    (hs : Ls ≫ u ≅ Vs) (ht : Lt ≫ u ≅ Vt)
    (h : m' ▷ u = hs.hom ≫ mq ≫ ht.inv) :
    m' ▷ u' =
      ((Bicategory.whiskerLeftIso Ls e).symm.trans hs).hom ≫ mq ≫
        ((Bicategory.whiskerLeftIso Lt e).symm.trans ht).inv := by
  rw [S2071WhiskerRight_base_iso_formula m' e, h]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Bicategory.whiskerLeftIso_hom, Bicategory.whiskerLeftIso_inv, Category.assoc]

end CoherenceLeg

/-! ## 2. Transport of the recorded witness along the leg `toY`

The cones of `mk toX toY x y c` and of `mk toX toY' x y c'` are the same data
(both structures only depend on the base legs `x` and `y`), so the transport
only has to rebuild `liftToY` and check the two projection equations. -/

section LegIso

/-- A cone of the square with leg `toY'` is a cone of the square with leg
`toY`.  The comparison 2-cell is unchanged because the base legs are unchanged. -/
noncomputable def S2108OldConeY {P X Y Z : EtaleStackPseudofunctor S1726K}
    (toX : Pseudofunctor.StrongTrans P X)
    (toY toY' : Pseudofunctor.StrongTrans P Y)
    (x : Pseudofunctor.StrongTrans X Z) (y : Pseudofunctor.StrongTrans Y Z)
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY y))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY' y))
    {W : EtaleStackPseudofunctor S1726K}
    (cone : (EtalePseudofunctorSquare.mk toX toY' x y c').Cone W) :
    (EtalePseudofunctorSquare.mk toX toY x y c).Cone W where
  toX := cone.toX
  toY := cone.toY
  commutes := cone.commutes

/-- A morphism of cones of the square with leg `toY'` is a morphism of cones of
the square with leg `toY`. -/
noncomputable def S2108OldConeMorphismY {P X Y Z : EtaleStackPseudofunctor S1726K}
    (toX : Pseudofunctor.StrongTrans P X)
    (toY toY' : Pseudofunctor.StrongTrans P Y)
    (x : Pseudofunctor.StrongTrans X Z) (y : Pseudofunctor.StrongTrans Y Z)
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY y))
    (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
      (Pseudofunctor.StrongTrans.vcomp toY' y))
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (EtalePseudofunctorSquare.mk toX toY' x y c').Cone W}
    (m : (EtalePseudofunctorSquare.mk toX toY' x y c').ConeMorphism s t) :
    (EtalePseudofunctorSquare.mk toX toY x y c).ConeMorphism
      (S2108OldConeY toX toY toY' x y c c' s)
      (S2108OldConeY toX toY toY' x y c c' t) where
  toX := m.toX
  toY := m.toY
  compatibility := m.compatibility

variable {P X Y Z : EtaleStackPseudofunctor S1726K}
variable (toX : Pseudofunctor.StrongTrans P X)
variable (toY toY' : Pseudofunctor.StrongTrans P Y)
variable (x : Pseudofunctor.StrongTrans X Z)
variable (y : Pseudofunctor.StrongTrans Y Z)
variable (e : Iso toY toY')
variable (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
  (Pseudofunctor.StrongTrans.vcomp toY y))
variable (c' : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
  (Pseudofunctor.StrongTrans.vcomp toY' y))

/-- **Transport of the recorded witness along the leg out of the apex**: if the
square with leg `toY` is a two-pullback, so is the square with the 2-isomorphic
leg `toY'`, for an arbitrary new comparison 2-cell `c'`.  The lift is unchanged;
the second comparison is composed with the whiskered 2-isomorphism. -/
noncomputable def S2108IsoWitnessY
    (w : (EtalePseudofunctorSquare.mk toX toY x y c).TwoPullbackWitness) :
    (EtalePseudofunctorSquare.mk toX toY' x y c').TwoPullbackWitness where
  lift W cone := w.lift W (S2108OldConeY toX toY toY' x y c c' cone)
  liftToX W cone := w.liftToX W (S2108OldConeY toX toY toY' x y c c' cone)
  liftToY W cone :=
    (S2058WhiskerLeft (w.lift W (S2108OldConeY toX toY toY' x y c c' cone)) e).symm.trans
      (w.liftToY W (S2108OldConeY toX toY toY' x y c c' cone))
  liftTwoCell W s t m :=
    w.liftTwoCell W (S2108OldConeY toX toY toY' x y c c' s)
      (S2108OldConeY toX toY toY' x y c c' t)
      (S2108OldConeMorphismY toX toY toY' x y c c' m)
  liftTwoCell_toX W s t m :=
    w.liftTwoCell_toX W (S2108OldConeY toX toY toY' x y c c' s)
      (S2108OldConeY toX toY toY' x y c c' t)
      (S2108OldConeMorphismY toX toY toY' x y c c' m)
  liftTwoCell_toY W s t m :=
    S2108LiftTwoCellToY (Bc := EtaleStackPseudofunctor S1726K)
      (w.liftTwoCell W (S2108OldConeY toX toY toY' x y c c' s)
        (S2108OldConeY toX toY toY' x y c c' t)
        (S2108OldConeMorphismY toX toY toY' x y c c' m)) e m.toY
      (w.liftToY W (S2108OldConeY toX toY toY' x y c c' s))
      (w.liftToY W (S2108OldConeY toX toY toY' x y c c' t))
      (w.liftTwoCell_toY W (S2108OldConeY toX toY toY' x y c c' s)
        (S2108OldConeY toX toY toY' x y c c' t)
        (S2108OldConeMorphismY toX toY toY' x y c c' m))
  twoCell_ext W first second alpha beta h1 h2 := by
    refine w.twoCell_ext W alpha beta h1 ?_
    exact S2071WhiskerRight_base_iso (Bc := EtaleStackPseudofunctor S1726K) e.symm h2

/-- **Transport of the full cone essential-surjectivity** along the leg out of
the apex. -/
theorem S2108EssSurjY
    (w : (EtalePseudofunctorSquare.mk toX toY x y c).TwoPullbackWitness)
    (h : S1827EssSurjOf (EtalePseudofunctorSquare.mk toX toY x y c) w) :
    S1827EssSurjOf (EtalePseudofunctorSquare.mk toX toY' x y c')
      (S2108IsoWitnessY toX toY toY' x y e c c' w) := by
  intro W cone f hX hY
  obtain ⟨hY'⟩ := hY
  exact h W (S2108OldConeY toX toY toY' x y c c' cone) f hX
    ⟨(S2058WhiskerLeft f e).trans hY'⟩

end LegIso

/-! ## 3. The base-pair swap preserves the full cone essential-surjectivity -/

section Swap

variable {P X Y Z : EtaleStackPseudofunctor S1726K}
variable (toX : Pseudofunctor.StrongTrans P X)
variable (toY : Pseudofunctor.StrongTrans P Y)
variable (x : Pseudofunctor.StrongTrans X Z)
variable (y : Pseudofunctor.StrongTrans Y Z)
variable (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
  (Pseudofunctor.StrongTrans.vcomp toY y))

/-- S2097's base-pair swap transports the recorded witness; it also transports
the full cone essential-surjectivity, because the cones of a square and of its
swap are exchanged on the nose. -/
theorem S2108SwapEssSurj
    (w : (EtalePseudofunctorSquare.mk toX toY x y c).TwoPullbackWitness)
    (h : S1827EssSurjOf (EtalePseudofunctorSquare.mk toX toY x y c) w) :
    S1827EssSurjOf (S2097SwappedSquare toX toY x y c)
      (S2097SwapWitness toX toY x y c w) := by
  intro W cone f hX hY
  exact h W (S2097OldCone toX toY x y c cone) f hY hX

end Swap

/-! ## 4. The pasted square of the butterfly

The pasted square of `S2097Pasting` has legs `Pg.projectionMap.transformation`
and `S2086Lift ; toB`, base legs `ptA ; f.map` and `g.map`, and comparison
2-cell `gamma`.  It is obtained from `Pg`'s square by the base-pair swap followed
by the leg change `Pg.toSource ~~> S2086Lift ; toB` along `S2097LiftToB`. -/

section BaseChange

variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

/-- The `toY` leg of the pasted square. -/
abbrev S2108ToY : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme)
    B.source.fiber :=
  Pseudofunctor.StrongTrans.vcomp (S2086Lift f g T ptA Pg) (toB f g)

/-- **Step 1: the base-pair swap.**  The weak witness of `Pg`'s square, read as
the witness of the square with the two base legs exchanged. -/
noncomputable def S2108SwappedWitness :
    (S2097SwappedSquare Pg.toSource Pg.projectionMap.transformation g.map
      (Pseudofunctor.StrongTrans.vcomp ptA f.map) Pg.commutes).TwoPullbackWitness :=
  S2097SwapWitness Pg.toSource Pg.projectionMap.transformation g.map
    (Pseudofunctor.StrongTrans.vcomp ptA f.map) Pg.commutes Pg.isPullback

/-- The full cone essential-surjectivity of the presentation, in the
`S1827EssSurjOf` form used by the transport.  This is a definitional identity:
both statements quantify over the same cones and the same recorded lift. -/
theorem S2108ConeEssSurjToEssSurj (h : S1852ConeEssSurj Pg) :
    S1827EssSurjOf (S1852WeakSquare Pg) Pg.isPullback := h

/-- **Step 1, full**: the swap preserves the full property. -/
theorem S2108SwappedFull (h : S1852ConeEssSurj Pg) :
    S1827EssSurjOf
      (S2097SwappedSquare Pg.toSource Pg.projectionMap.transformation g.map
        (Pseudofunctor.StrongTrans.vcomp ptA f.map) Pg.commutes)
      (S2108SwappedWitness f g T ptA Pg) :=
  S2108SwapEssSurj Pg.toSource Pg.projectionMap.transformation g.map
    (Pseudofunctor.StrongTrans.vcomp ptA f.map) Pg.commutes Pg.isPullback
    (S2108ConeEssSurjToEssSurj f g T ptA Pg h)

/-- **Step 2: the leg change.**  The weak witness of the pasted square,
obtained from the swapped presentation square by replacing `Pg.toSource` with
`S2086Lift ; toB` along `S2097LiftToB`.  The comparison 2-cell is
`S2097Pasting`'s `gamma`; no coherence between `gamma` and `Pg.commutes` is
required by the transport. -/
noncomputable def S2108PastedWitness :
    (S2097Pasting f g T ptA Pg).squareP.TwoPullbackWitness :=
  S2108IsoWitnessY
    (toX := Pg.projectionMap.transformation)
    (toY := Pg.toSource)
    (toY' := S2108ToY f g T ptA Pg)
    (x := Pseudofunctor.StrongTrans.vcomp ptA f.map)
    (y := g.map)
    (e := (S2097LiftToB f g T ptA Pg).symm)
    (c := Pg.commutes.symm)
    (c' := (S2097Pasting f g T ptA Pg).gamma)
    (S2108SwappedWitness f g T ptA Pg)

/-- **Step 2, full**: the full property transports along the leg change. -/
theorem S2108PastedFull (h : S1852ConeEssSurj Pg) :
    S1827EssSurjOf (S2097Pasting f g T ptA Pg).squareP
      (S2108PastedWitness f g T ptA Pg) :=
  S2108EssSurjY
    (toX := Pg.projectionMap.transformation)
    (toY := Pg.toSource)
    (toY' := S2108ToY f g T ptA Pg)
    (x := Pseudofunctor.StrongTrans.vcomp ptA f.map)
    (y := g.map)
    (e := (S2097LiftToB f g T ptA Pg).symm)
    (c := Pg.commutes.symm)
    (c' := (S2097Pasting f g T ptA Pg).gamma)
    (S2108SwappedWitness f g T ptA Pg)
    (S2108SwappedFull f g T ptA Pg h)

/-- **The pasted-square full datum**: the weak witness and the full cone
essential-surjectivity of the pasted square, transported from the presentation's
recorded `isPullback` and its `S1852ConeEssSurj`. -/
noncomputable def S2108PastedSquareFull (h : S1852ConeEssSurj Pg) :
    S2097PastedSquareFull f g T ptA Pg where
  witness := S2108PastedWitness f g T ptA Pg
  full := S2108PastedFull f g T ptA Pg h

end BaseChange

/-! ## 5. The `pastedTransport` field and the reduced input bundle -/

/-- **The function implementing `S2097TwoFullInputs.pastedTransport`.** -/
noncomputable def S2108PastedTransport :
    ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
      (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
      S1852ConeEssSurj Pg → S2097PastedSquareFull f g T ptA Pg :=
  fun A B C f g T ptA Pg =>
    S2108PastedSquareFull (A := A) (B := B) (C := C) f g T ptA Pg

/-- **The S2097 input bundle, with the transport constructed**: only S2094's two
full inputs are needed. -/
noncomputable def S2108TwoFullInputs
    (hBig : S2094BigSquareEssSurj) (hG : S2094GPresentationConeEssSurj) :
    S2097TwoFullInputs where
  bigSquare := hBig
  gPresentation := hG
  pastedTransport := fun A B C f g T ptA Pg =>
    S2108PastedSquareFull (A := A) (B := B) (C := C) f g T ptA Pg

/-- **The butterfly theorem with only `S2097RightCancelStatement` missing.**
S2094's big-square essential-surjectivity, S2094's presentation
cone-essential-surjectivity and the right-cancellation lemma give
`S2086BaseChangePullback hg` for every `hg`.  The square transport is now a
theorem, not an assumption. -/
noncomputable def S2108BaseChangePullback_of_rightCancel
    (hRC : S2097RightCancelStatement)
    (hBig : S2094BigSquareEssSurj)
    (hG : S2094GPresentationConeEssSurj)
    (hg : S2086CospanGMapFiniteEtale) : S2086BaseChangePullback hg :=
  S2097BaseChangePullback_of_twoFullInputs (S2108TwoFullInputs hBig hG) hRC hg

/-! ## 6. Checks and axiom audit -/

#check @S2108LiftTwoCellToY
#check @S2108IsoWitnessY
#check @S2108EssSurjY
#check @S2108SwapEssSurj
#check @S2108PastedWitness
#check @S2108PastedSquareFull
#check @S2108PastedTransport
#check @S2108TwoFullInputs
#check @S2108BaseChangePullback_of_rightCancel

#print axioms S2108LiftTwoCellToY
#print axioms S2108IsoWitnessY
#print axioms S2108EssSurjY
#print axioms S2108SwapEssSurj
#print axioms S2108PastedWitness
#print axioms S2108PastedFull
#print axioms S2108PastedSquareFull
#print axioms S2108PastedTransport
#print axioms S2108TwoFullInputs
#print axioms S2108BaseChangePullback_of_rightCancel

end LeanFormal.IUT.XiFPaper.S2108PastedTransportActual

end
