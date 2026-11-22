import tmp.sheaf.xif.paper.S2094FullUniversalInputsActual

/-!
# S2097: the butterfly base-change witness and the exact 2-categorical missing

## The target

`S2086BaseChangePullback hg` asks, for every cospan of actual cover maps
`f : A ⟶ C`, `g : B ⟶ C`, every test scheme `T`, every point
`ptA : h_T ⟶ A.source` and every `g`-base-change presentation `Pg` at
`ptA ; f.map`, that the explicit square

  Pg.pullbackScheme --S2086Lift--> A ×_C B
        |                              |
  Pg.projectionMap                     toA
        v                              v
        T ------------ptA------------> A

is a recorded `TwoPullbackWitness` (the butterfly identification
`T ×_A (A ×_C B) = T ×_C B`).

## What is proved here

* `S2097LiftToB`: S2076's second projection of `S2086Lift`; this is the
  comparison `S2086Lift ; toB ≅ Pg.toSource` needed to build the pasted
  square.
* `S2097Pasting`: the pasting datum whose top square is the *swap* of the
  desired square (legs `projectionMap` and `S2086Lift`), whose bottom square
  is the iso-comma square `(toA, toB, f.map, g.map)`, and whose pasted square
  is `Pg`'s square with the two base objects swapped and `toSource` replaced
  by `S2086Lift ; toB` along `S2097LiftToB`.
* `S2097SwapWitness`: swapping the two legs of any square preserves the
  recorded weak witness.  Applied to the pasted datum it turns a witness for
  the swap of the desired square into a witness for the desired square.
* `S2097BaseChangePullback_of_rightCancel`: the conditional butterfly
  theorem.  It assumes
    1. `S1827EssSurjOf` of the iso-comma square (`hBig`), which is exactly
       `S2094BigSquareEssSurj`;
    2. a weak witness together with `S1827EssSurjOf` for the pasted square
       (`hPst`; this is the square-isomorphic transport of `Pg.isPullback`
       and `S1852ConeEssSurj Pg`);
    3. the reverse-pasting (right-cancellation) 2-categorical lemma
       `S2097RightCancelStatement`.
  It concludes the fully constructed `S2086ToASquare` witness.
* `S2097BaseChangePullback_of_inputs` and
  `S2097BaseChangePullback_of_twoFullInputs` assemble the global conditional
  statement for every `hg`.

## The exact first missing

`S2097RightCancelStatement` is the precise missing 2-categorical input:
for every pasting datum `D`, the weak witness and the full cone
essential-surjectivity of the bottom square `D.square2`, together with the
same data for the pasted square `D.squareP`, give a weak witness for the top
square `D.square1`.

This is the *reverse* direction of S2071.  S2071 proves that the witnesses of
the two factor squares give the witness of the pasted square; it cannot be
run backwards, and in the butterfly configuration the two factor squares share
the leg `B ⟶ C` at different apices with two triangle 2-cells, so the
forward pasting statement does not apply.  The recorded seven fields alone do
not imply the missing cone comparison (S1827, S1843, S1844, S1850, S1852);
neither does the forward pasting S2071.  The transport in item 2 is a square-isomorphism transport from the two S2094
inputs; this file states it precisely but does not formalize it.  It is not the
missing 2-categorical lemma.

## Honest boundary

No `sorry`, no new axiom, no fabricated weak witness, and no unconditional
claim of `S2086BaseChangePullback`.  The target is reduced to a named,
non-tautological 2-categorical lemma; the lemma is not asserted.  The auxiliary
square transport `pastedTransport` is also not formalized.  The axiom
footprint of every conditional theorem is `propext`, `Classical.choice` and
`Quot.sound` (see the audit at the end).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1843SourceAllPointsActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual

universe u

def S2097RightCancelStatement : Type 1 :=
  forall (D : S2058Pasting (F := S1726K)),
    forall (w2 : D.square2.TwoPullbackWitness),
      S1827EssSurjOf D.square2 w2 ->
      forall (wP : D.squareP.TwoPullbackWitness),
        S1827EssSurjOf D.squareP wP ->
        D.square1.TwoPullbackWitness

section Swap

variable {P X Y Z : EtaleStackPseudofunctor S1726K}
variable (toX : Pseudofunctor.StrongTrans P X)
variable (toY : Pseudofunctor.StrongTrans P Y)
variable (x : Pseudofunctor.StrongTrans X Z)
variable (y : Pseudofunctor.StrongTrans Y Z)
variable (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x)
  (Pseudofunctor.StrongTrans.vcomp toY y))

abbrev S2097SwappedSquare : EtalePseudofunctorSquare P Y X Z :=
  EtalePseudofunctorSquare.mk toY toX y x c.symm

noncomputable def S2097OldCone {W : EtaleStackPseudofunctor S1726K}
    (cone : (S2097SwappedSquare toX toY x y c).Cone W) :
    (EtalePseudofunctorSquare.mk toX toY x y c).Cone W where
  toX := cone.toY
  toY := cone.toX
  commutes := cone.commutes.symm

noncomputable def S2097OldConeMorphism {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2097SwappedSquare toX toY x y c).Cone W}
    (m : (S2097SwappedSquare toX toY x y c).ConeMorphism s t) :
    (EtalePseudofunctorSquare.mk toX toY x y c).ConeMorphism
      (S2097OldCone toX toY x y c s) (S2097OldCone toX toY x y c t) where
  toX := m.toY
  toY := m.toX
  compatibility := by
    have h := m.compatibility
    change Pseudofunctor.StrongTrans.whiskerRight m.toY x ≫ t.commutes.inv =
      s.commutes.inv ≫ Pseudofunctor.StrongTrans.whiskerRight m.toX y
    calc
      Pseudofunctor.StrongTrans.whiskerRight m.toY x ≫ t.commutes.inv
          = (s.commutes.inv ≫ s.commutes.hom) ≫
              (Pseudofunctor.StrongTrans.whiskerRight m.toY x ≫ t.commutes.inv) := by
              rw [Iso.inv_hom_id, Category.id_comp]
      _ = s.commutes.inv ≫
            ((s.commutes.hom ≫ Pseudofunctor.StrongTrans.whiskerRight m.toY x) ≫
              t.commutes.inv) := by
              rw [Category.assoc, Category.assoc]
      _ = s.commutes.inv ≫
            ((Pseudofunctor.StrongTrans.whiskerRight m.toX y ≫ t.commutes.hom) ≫
              t.commutes.inv) := by
              rw [← h]
      _ = s.commutes.inv ≫ Pseudofunctor.StrongTrans.whiskerRight m.toX y := by
              rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

noncomputable def S2097SwapWitness
    (w : (EtalePseudofunctorSquare.mk toX toY x y c).TwoPullbackWitness) :
    (S2097SwappedSquare toX toY x y c).TwoPullbackWitness where
  lift W cone := w.lift W (S2097OldCone toX toY x y c cone)
  liftToX W cone := w.liftToY W (S2097OldCone toX toY x y c cone)
  liftToY W cone := w.liftToX W (S2097OldCone toX toY x y c cone)
  liftTwoCell W s t m :=
    w.liftTwoCell W (S2097OldCone toX toY x y c s) (S2097OldCone toX toY x y c t)
      (S2097OldConeMorphism toX toY x y c m)
  liftTwoCell_toX W s t m :=
    w.liftTwoCell_toY W (S2097OldCone toX toY x y c s) (S2097OldCone toX toY x y c t)
      (S2097OldConeMorphism toX toY x y c m)
  liftTwoCell_toY W s t m :=
    w.liftTwoCell_toX W (S2097OldCone toX toY x y c s) (S2097OldCone toX toY x y c t)
      (S2097OldConeMorphism toX toY x y c m)
  twoCell_ext W first second alpha beta h1 h2 :=
    w.twoCell_ext W alpha beta h2 h1

end Swap

section BaseChange

variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

noncomputable def S2097LiftToB :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2086Lift f g T ptA Pg) (toB f g))
      Pg.toSource :=
  (S2076Witness (f := f) (g := g)).liftToY
    (schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme)
    (S2086Cone f g T ptA Pg)

noncomputable def S2097Pasting : S2058Pasting (F := S1726K) where
  P := schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme
  X := schemeRepresentableEtalePseudofunctor S1726K T
  Ys := sitePseudofunctor f g
  Zs := A.source.fiber
  Y2 := B.source.fiber
  Z2 := C.source.fiber
  toX1 := Pg.projectionMap.transformation
  toY1 := S2086Lift f g T ptA Pg
  x1 := ptA
  xi := toA f g
  c1 := (S2086LiftToA f g T ptA Pg).symm
  toY2 := toB f g
  x2 := f.map
  y2 := g.map
  c2 := commutes f g
  gamma := (S2058AssociatorIso Pg.projectionMap.transformation ptA f.map).symm.trans
    ((S2086Cone f g T ptA Pg).commutes.trans
      (S2058WhiskerRight (S2097LiftToB f g T ptA Pg) g.map).symm)

structure S2097PastedSquareFull : Type 1 where
  witness : (S2097Pasting f g T ptA Pg).squareP.TwoPullbackWitness
  full : S1827EssSurjOf (S2097Pasting f g T ptA Pg).squareP witness

noncomputable def S2097BaseChangePullback_of_rightCancel
    (hRC : S2097RightCancelStatement)
    (hBig : S2094BigSquareEssSurj)
    (hPst : S2097PastedSquareFull f g T ptA Pg) :
    (S2086ToASquare f g T ptA Pg).TwoPullbackWitness := by
  let D := S2097Pasting f g T ptA Pg
  have hQ : S1827EssSurjOf D.square2 (S2076Witness (f := f) (g := g)) := by
    change S1827EssSurjOf (S2076Square f g) (S2076Witness (f := f) (g := g))
    exact hBig A B C f g
  have hw : D.square1.TwoPullbackWitness :=
    hRC D (S2076Witness (f := f) (g := g)) hQ hPst.witness hPst.full
  exact S2097SwapWitness (Pg.projectionMap.transformation) (S2086Lift f g T ptA Pg)
    (ptA) (toA f g) ((S2086LiftToA f g T ptA Pg).symm) hw

end BaseChange

section Global

open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual

/-- The two missing data of the butterfly reduction, bundled:
* the reverse-pasting (right-cancellation) 2-categorical lemma;
* the weak witness together with the full cone essential-surjectivity of the
  pasted square (the square-isomorphic transport of the `g`-presentation's
  `isPullback` and `S1852ConeEssSurj`).
The second item is bookkeeping along the explicit square isomorphism; the first
is the genuine missing 2-categorical lemma. -/
structure S2097ButterflyMissing : Type 1 where
  rightCancel : S2097RightCancelStatement
  pastedFull : forall (A B C : S1728Cover) (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
    S2097PastedSquareFull f g T ptA Pg


/-- **The conditional butterfly theorem**: S2094's big-square essential
surjectivity, the pasted-square full data and the missing right-cancellation
lemma give `S2086BaseChangePullback hg` for every `hg`. -/
noncomputable def S2097BaseChangePullback_of_inputs
    (hRC : S2097RightCancelStatement)
    (hBig : S2094BigSquareEssSurj)
    (hPst : forall (A B C : S1728Cover) (f : S1728CoverMap A C)
      (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
      (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
      S2097PastedSquareFull f g T ptA Pg)
    (hg : S2086CospanGMapFiniteEtale) : S2086BaseChangePullback hg := by
  intro A B C f g T ptA
  exact S2097BaseChangePullback_of_rightCancel f g T ptA
    ((hg A B C f g).baseChange T (S2086PointC f ptA)) hRC hBig
    (hPst A B C f g T ptA ((hg A B C f g).baseChange T (S2086PointC f ptA)))

/-- The bundled missing data gives the conditional butterfly theorem. -/
noncomputable def S2097BaseChangePullback_of_missing
    (h : S2097ButterflyMissing) (hBig : S2094BigSquareEssSurj)
    (hg : S2086CospanGMapFiniteEtale) : S2086BaseChangePullback hg :=
  S2097BaseChangePullback_of_inputs h.rightCancel hBig h.pastedFull hg


/-- The two S2094 full inputs, together with the square-isomorphic transport
from the `g`-presentation to the pasted square.  The transport is not a new
2-categorical obstruction: the pasted square is `Pg`'s square with the two
base objects swapped and `toSource` replaced by `S2086Lift ; toB` along
`S2097LiftToB`. -/
structure S2097TwoFullInputs : Type 1 where
  /-- S2094 input 1: `S1827EssSurjOf` for the iso-comma square. -/
  bigSquare : S2094BigSquareEssSurj
  /-- S2094 input 2: `S1852ConeEssSurj` for every used `g`-presentation. -/
  gPresentation : S2094GPresentationConeEssSurj
  /-- The square-isomorphic transport of the presentation's weak witness and
  full property to the pasted square. -/
  pastedTransport : forall (A B C : S1728Cover) (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
    S1852ConeEssSurj Pg -> S2097PastedSquareFull f g T ptA Pg

/-- **The butterfly theorem from the two full S2094 inputs and the missing
right-cancellation lemma.**  This is the precise reduction promised in the
header: the only genuine missing 2-categorical input is `hRC`; the other two
inputs are exactly S2094's `S1827EssSurjOf` and `S1852ConeEssSurj`, plus the
explicit square transport. -/
noncomputable def S2097BaseChangePullback_of_twoFullInputs
    (h : S2097TwoFullInputs) (hRC : S2097RightCancelStatement)
    (hg : S2086CospanGMapFiniteEtale) : S2086BaseChangePullback hg := by
  refine S2097BaseChangePullback_of_inputs hRC h.bigSquare ?_ hg
  intro A B C f g T ptA Pg
  exact h.pastedTransport A B C f g T ptA Pg
    (h.gPresentation A B C f g T ptA Pg)

end Global

#check S2097TwoFullInputs
#check S2097BaseChangePullback_of_twoFullInputs
#check S2097ButterflyMissing
#check S2097BaseChangePullback_of_inputs
#check S2097BaseChangePullback_of_missing
#check S1827EssSurjNotFromWitness
#check S1843RightCancelNotFromWitness
#check S1852NotFirstMissing
#check S2097RightCancelStatement
#check @S2097SwapWitness
#check @S2097Pasting
#check @S2097BaseChangePullback_of_rightCancel

#print axioms S2097BaseChangePullback_of_twoFullInputs
#print axioms S2097BaseChangePullback_of_inputs
#print axioms S2097BaseChangePullback_of_missing
#print axioms S2097SwapWitness
#print axioms S2097BaseChangePullback_of_rightCancel

end LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual

end
