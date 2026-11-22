import tmp.sheaf.xif.paper.S2107RightCancelActual
import tmp.sheaf.xif.paper.S2108PastedTransportActual
import tmp.sheaf.xif.paper.S2104ButterflyTwistActual

/-!
# S2114: the canonical lift 2-cell in the actual butterfly configuration

## The target

S2107 reduced `S2097RightCancelStatement` to
`S2107CanonicalLiftTwoCell D w2 h2 wP`: for every morphism `m` of cones over
the lower square of a pasting datum `D`, a 2-cell

  `sigma : S2107ExtLift wP s -> S2107ExtLift wP t`

whose two projections are prescribed by `m` and by the canonical comparisons
`S2107ExtLiftToX` and `S2107ExtLiftToY`.

This file studies that target in the *actual* S2095/S2097 butterfly datum

  `D = S2097Pasting f g T ptA Pg`,   `w2 = S2076Witness`,   `wP = S2108PastedWitness`,

whose apex `D.P` is the representable stack of `Pg.pullbackScheme` and whose
upper square is the iso-comma square.  The canonical twist for the actual
butterfly (S2104/S2099TwistAt_canonical) is the canonical instance of the
comparison compatibility that the missing equation needs.

## What is proved here (unconditionally, no sorry, no new axiom)

1. `S2114PastedConeCompat`: the bicategorical coherence that makes a morphism
   `m` of cones over the lower square induce a morphism of cones over the
   pasted square.  It is stated in an arbitrary bicategory, from
   `whiskerRight_comp`, `comp_whiskerRight`, the cone-morphism compatibility
   and the coherence of right whiskering along the pasting 2-cell `c2`.

2. `S2114ExtConeHom`, `S2114PastedTwoCell`, `S2114PastedTwoCell_toX`,
   `S2114PastedTwoCell_toY2`: in the actual datum, the pasted witness gives,
   for every `m`, a 2-cell `sigma0` between the canonical lifts together with
   its two *available* projection equations: along `D.toX1` and along
   `D.toY1 ; D.toY2`.

3. `Coherence.S2114LowerLiftToACompat`: the associativity coherence for the
   toA-whiskering of the pasted action.  It rewrites the composite of `sigma0`
   with the lower leg and the upper first leg into the explicit comparison
   composite of `S2107LiftToYIsoX`, using the pasted first projection equation,
   the cone-morphism compatibility and the lower pasting iso.

4. `S2114CanonicalLiftTwoCell_of_toYEquation` and
   `S2114ToYEquation_of_canonicalLift`: because the apex `D.P` is
   representable, the 2-cell type
   `S2107ExtLift wP s -> S2107ExtLift wP t` is a subsingleton
   (`S1897Modification_subsingleton_representable`).  Hence
   `S2107CanonicalLiftTwoCell D w2 h2 wP` is *equivalent* to the single
   equation family `S2114ToYEquation`: the pasted 2-cell `sigma0` itself must
   satisfy the `D.toY1` projection equation.  This is the exact remaining
   content; the first projection equation and the composite equation already
   hold.

5. `S2114ToAWitness_of_canonicalLift` and
   `S2114ToAWitness_of_toYEquation`: the actual base-change square
   `S2086ToASquare f g T ptA Pg` has a two-pullback witness as soon as the
   canonical lift 2-cell (equivalently `S2114ToYEquation`) is available.  This
   is S2097's assembly specialised to the actual datum.

## The exact first missing

`S2114ToYEquation` is the precise missing equation.  It is *not* the upper
square's own essential surjectivity and it is *not* the canonical twist S2104:
`S2104ToBButterflyCanonicalTwist` concerns the canonical lift
`gLiftSite (S2095ToBCone ...)` and its canonical comparisons
`gLiftToA`/`gLiftToB`, while `S2107ExtLiftToY` is built from
`Classical.choice` applied to the *given* essential surjectivity `h2`.  The
recorded weak fields do not relate the chosen comparison isomorphisms to the
cone's commutes cell (S2099 isolates exactly this twist; S1801 records that the
seven witness fields do not export the 2-cell fullness / compatible lift).  The
canonical twist is the one case where the compatibility is known
(`S2099TwistAt_canonical`, exported to the actual butterfly as
`S2104ToBButterflyCanonicalTwist`); it does not identify the choice made by
`h2`.

Accordingly the 2-cell fullness `S2114UpperTwoCellSurjTo` (S1801
`TwoCellSurjTo` for the actual iso-comma square) and the actual twist
`S2114UpperCompatibleLift` are recorded here as the standard upper-square
inputs.  They supply *compatible comparisons*; the additional interaction with
the pasted lift action is precisely `S2114ToYEquation`.

A stronger, upper-square-shaped sufficient datum is also recorded:
`S2114ChosenComparisonCompat` says that the comparison chosen by `h2` has the
prescribed projections onto the two upper legs of the actual iso-comma square
(the compatible-lift condition of S2099/S1801 at the *specific* classical
choice).  The canonical instance of this compatibility is the twist of
S2099/S2104, and the pointwise identification of the twist with the
comma-morphism condition is proved here as `S2114UpperTwistAt_iff_comma`.
`S2114ChosenComparisonCompat` is a named missing statement; no inhabitant is
produced.  No fake 2-cell, witness or axiom is added.

## Axiom footprint

Only `propext`, `Classical.choice`, `Quot.sound`; see the audit at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace LeanFormal.IUT.XiFPaper.S2114CanonicalLiftTwoCellActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual
open LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2108PastedTransportActual

universe u

/-! ## 1. A bicategorical coherence for the pasted cone morphism -/

namespace Coherence

universe v w

variable {Bc : Type w} [Bicategory.{v, w} Bc]

/-- **Compatibility of the cone morphism over the pasted square.** -/
theorem S2114PastedConeCompat
    {a X Y Z Y2 Z2 : Bc}
    {sX tX : a ⟶ X} (nn : sX ⟶ tX)
    {sY tY : a ⟶ Y} (mq : sY ⟶ tY)
    (x1 : X ⟶ Z) (x2 : Z ⟶ Z2)
    (xi : Y ⟶ Z) (toY2 : Y ⟶ Y2) (y2 : Y2 ⟶ Z2)
    (c2 : xi ≫ x2 ≅ toY2 ≫ y2)
    (cs0 : sX ≫ x1 ≅ sY ≫ xi) (ct0 : tX ≫ x1 ≅ tY ≫ xi)
    (hcomp : (nn ▷ x1) ≫ ct0.hom = cs0.hom ≫ (mq ▷ xi)) :
    (nn ▷ (x1 ≫ x2)) ≫
      ((α_ tX x1 x2).inv ≫ (ct0.hom ▷ x2) ≫ (α_ tY xi x2).hom ≫
        (tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv)
    =
    ((α_ sX x1 x2).inv ≫ (cs0.hom ▷ x2) ≫ (α_ sY xi x2).hom ≫
        (sY ◁ c2.hom) ≫ (α_ sY toY2 y2).inv) ≫
      ((mq ▷ toY2) ▷ y2) := by
  have h4 : ((mq ▷ xi) ▷ x2) ≫ (α_ tY xi x2).hom =
      (α_ sY xi x2).hom ≫ (mq ▷ (xi ≫ x2)) := by
    rw [whiskerRight_comp mq xi x2]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h5 : (mq ▷ (xi ≫ x2)) ≫ (tY ◁ c2.hom) =
      (sY ◁ c2.hom) ≫ (mq ▷ (toY2 ≫ y2)) := by
    have h := LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual.Coherence.S2071WhiskerRight_base_iso_formula (al := mq) (u := xi ≫ x2)
      (u' := toY2 ≫ y2) c2
    have key : (sY ◁ c2.hom) ≫ (sY ◁ c2.inv) = 𝟙 _ := by
      rw [← Bicategory.whiskerLeft_comp, c2.hom_inv_id, Bicategory.whiskerLeft_id]
    rw [h, ← Category.assoc, key, Category.id_comp]
  have h6 : (mq ▷ (toY2 ≫ y2)) ≫ (α_ tY toY2 y2).inv =
      (α_ sY toY2 y2).inv ≫ ((mq ▷ toY2) ▷ y2) := by
    rw [whiskerRight_comp mq toY2 y2]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hstep : ((nn ▷ x1) ▷ x2) ≫ (ct0.hom ▷ x2) =
      ((nn ▷ x1) ≫ ct0.hom) ▷ x2 :=
    (comp_whiskerRight (nn ▷ x1) ct0.hom x2).symm
  have hmain :
      ((nn ▷ x1) ▷ x2) ≫
        ((ct0.hom ▷ x2) ≫ ((α_ tY xi x2).hom ≫
          ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv))) =
      (cs0.hom ▷ x2) ≫ ((α_ sY xi x2).hom ≫
        ((sY ◁ c2.hom) ≫ ((α_ sY toY2 y2).inv ≫ ((mq ▷ toY2) ▷ y2)))) := by
    calc
      ((nn ▷ x1) ▷ x2) ≫
          ((ct0.hom ▷ x2) ≫ ((α_ tY xi x2).hom ≫
            ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv)))
          = (((nn ▷ x1) ▷ x2) ≫ (ct0.hom ▷ x2)) ≫
              ((α_ tY xi x2).hom ≫ ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv)) := by
            rw [Category.assoc]
      _ = ((((nn ▷ x1) ≫ ct0.hom)) ▷ x2) ≫
              ((α_ tY xi x2).hom ≫ ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv)) := by
            rw [hstep]
      _ = (((cs0.hom ≫ (mq ▷ xi))) ▷ x2) ≫
              ((α_ tY xi x2).hom ≫ ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv)) := by
            rw [hcomp]
      _ = ((cs0.hom ▷ x2) ≫ ((mq ▷ xi) ▷ x2)) ≫
              ((α_ tY xi x2).hom ≫ ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv)) := by
            rw [comp_whiskerRight]
      _ = (cs0.hom ▷ x2) ≫ (((mq ▷ xi) ▷ x2) ≫
              ((α_ tY xi x2).hom ≫ ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv))) := by
            rw [Category.assoc]
      _ = (cs0.hom ▷ x2) ≫ ((((mq ▷ xi) ▷ x2) ≫ (α_ tY xi x2).hom) ≫
              ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv)) := by
            rw [Category.assoc]
      _ = (cs0.hom ▷ x2) ≫ (((α_ sY xi x2).hom ≫ (mq ▷ (xi ≫ x2))) ≫
              ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv)) := by
            rw [h4]
      _ = (cs0.hom ▷ x2) ≫ ((α_ sY xi x2).hom ≫ ((mq ▷ (xi ≫ x2)) ≫
              ((tY ◁ c2.hom) ≫ (α_ tY toY2 y2).inv))) := by
            rw [Category.assoc]
      _ = (cs0.hom ▷ x2) ≫ ((α_ sY xi x2).hom ≫ (((mq ▷ (xi ≫ x2)) ≫ (tY ◁ c2.hom)) ≫
              (α_ tY toY2 y2).inv)) := by
            rw [Category.assoc]
      _ = (cs0.hom ▷ x2) ≫ ((α_ sY xi x2).hom ≫ (((sY ◁ c2.hom) ≫ (mq ▷ (toY2 ≫ y2))) ≫
              (α_ tY toY2 y2).inv)) := by
            rw [h5]
      _ = (cs0.hom ▷ x2) ≫ ((α_ sY xi x2).hom ≫ ((sY ◁ c2.hom) ≫ ((mq ▷ (toY2 ≫ y2)) ≫
              (α_ tY toY2 y2).inv))) := by
            rw [Category.assoc]
      _ = (cs0.hom ▷ x2) ≫ ((α_ sY xi x2).hom ≫ ((sY ◁ c2.hom) ≫
              ((α_ sY toY2 y2).inv ≫ ((mq ▷ toY2) ▷ y2)))) := by
            rw [h6]
  rw [whiskerRight_comp nn x1 x2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hmain]

/-- **The toA-whiskering of the pasted action.**  The composite of the pasted
2-cell with the lower leg and then with the upper first leg is the explicit
comparison composite used in S2107LiftToYIsoX.  This is the associativity
coherence behind S2107LiftToYIsoX; it uses the pasted first projection
equation, the cone-morphism compatibility and the lower pasting iso. -/
theorem S2114LowerLiftToACompat
    {a P X Y Z : Bc}
    {l_s l_t : a ⟶ P} (wtc : l_s ⟶ l_t)
    (p : P ⟶ X) (q : P ⟶ Y) (x : X ⟶ Z) (z : Y ⟶ Z)
    (c1 : p ≫ x ≅ q ≫ z)
    {sX tX : a ⟶ X} (nn : sX ⟶ tX)
    {sY tY : a ⟶ Y} (mq : sY ⟶ tY)
    (a_s : l_s ≫ p ≅ sX) (a_t : l_t ≫ p ≅ tX)
    (c_s : sX ≫ x ≅ sY ≫ z) (c_t : tX ≫ x ≅ tY ≫ z)
    (hWT : wtc ▷ p = a_s.hom ≫ nn ≫ a_t.inv)
    (hcomp : (nn ▷ x) ≫ c_t.hom = c_s.hom ≫ (mq ▷ z)) :
    (wtc ▷ q) ▷ z =
      ((α_ l_s q z).hom ≫ (l_s ◁ c1.inv) ≫ (α_ l_s p x).inv ≫
          (a_s.hom ▷ x) ≫ c_s.hom) ≫
        (mq ▷ z) ≫
      (c_t.inv ≫ (a_t.inv ▷ x) ≫ (α_ l_t p x).hom ≫
          (l_t ◁ c1.hom) ≫ (α_ l_t q z).inv) := by
  have hnnx : (nn ▷ x) = c_s.hom ≫ (mq ▷ z) ≫ c_t.inv := by
    rw [← Category.assoc, ← hcomp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsplit : (wtc ▷ q) ▷ z =
      (α_ l_s q z).hom ≫ (wtc ▷ (q ≫ z)) ≫ (α_ l_t q z).inv := by
    rw [whiskerRight_comp wtc q z]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hbase : wtc ▷ (q ≫ z) =
      (l_s ◁ c1.inv) ≫ (wtc ▷ (p ≫ x)) ≫ (l_t ◁ c1.hom) :=
    LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual.Coherence.S2071WhiskerRight_base_iso_formula (al := wtc) (u := p ≫ x) (u' := q ≫ z) c1
  have hmid : wtc ▷ (p ≫ x) =
      (α_ l_s p x).inv ≫ ((wtc ▷ p) ▷ x) ≫ (α_ l_t p x).hom :=
    whiskerRight_comp wtc p x
  have hWTx : (wtc ▷ p) ▷ x = (a_s.hom ▷ x) ≫ (nn ▷ x) ≫ (a_t.inv ▷ x) := by
    rw [hWT]
    simp only [comp_whiskerRight]
  rw [hsplit, hbase, hmid, hWTx, hnnx]
  simp only [Category.assoc]

end Coherence

/-! ## 2. The actual S2095/S2097 butterfly datum -/

section Actual

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

/-- The actual butterfly pasting datum of S2097: lower square the explicit
butterfly square, upper square the iso-comma square, pasted square the
presentation square (swapped, with `toSource` replaced by `S2086Lift ; toB`). -/
abbrev S2114D : S2058Pasting (F := S1726K) := S2097Pasting f g T ptA Pg

/-- The recorded weak two-pullback witness of the actual pasted square
(S2108's transport of `Pg.isPullback`). -/
abbrev S2114WP : (S2114D f g T ptA Pg).squareP.TwoPullbackWitness :=
  S2108PastedWitness f g T ptA Pg

/-- The recorded canonical two-pullback witness of the actual upper (iso-comma)
square. -/
abbrev S2114W2 : (S2114D f g T ptA Pg).square2.TwoPullbackWitness :=
  S2076Witness (f := f) (g := g)

/-- The actual lower-square cone morphism over the pasted square: `toX` is
`m.toX`, and `toY` is `m.toY` whiskered by `D.toY2`; the compatibility is
`S2114PastedConeCompat`. -/
noncomputable def S2114ExtConeHom {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2114D f g T ptA Pg).square1.Cone W}
    (m : (S2114D f g T ptA Pg).square1.ConeMorphism s t) :
    (S2114D f g T ptA Pg).squareP.ConeMorphism
      (S2107ExtCone (S2114D f g T ptA Pg) s)
      (S2107ExtCone (S2114D f g T ptA Pg) t) where
  toX := m.toX
  toY := m.toY ▷ (S2114D f g T ptA Pg).toY2
  compatibility := by
    exact Coherence.S2114PastedConeCompat
      (Bc := EtaleStackPseudofunctor S1726K)
      (nn := m.toX) (mq := m.toY)
      (x1 := (S2114D f g T ptA Pg).x1) (x2 := (S2114D f g T ptA Pg).x2)
      (xi := (S2114D f g T ptA Pg).xi)
      (toY2 := (S2114D f g T ptA Pg).toY2) (y2 := (S2114D f g T ptA Pg).y2)
      (c2 := (S2114D f g T ptA Pg).c2)
      (cs0 := s.commutes) (ct0 := t.commutes) m.compatibility

/-- The 2-cell `sigma0` produced by the pasted witness. -/
noncomputable def S2114PastedTwoCell {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2114D f g T ptA Pg).square1.Cone W}
    (m : (S2114D f g T ptA Pg).square1.ConeMorphism s t) :
    S2107ExtLift (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) s ⟶
      S2107ExtLift (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) t :=
  (S2114WP f g T ptA Pg).liftTwoCell W
    (S2107ExtCone (S2114D f g T ptA Pg) s)
    (S2107ExtCone (S2114D f g T ptA Pg) t)
    (S2114ExtConeHom f g T ptA Pg m)

/-- The first available projection equation of `sigma0`. -/
theorem S2114PastedTwoCell_toX {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2114D f g T ptA Pg).square1.Cone W}
    (m : (S2114D f g T ptA Pg).square1.ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2114PastedTwoCell f g T ptA Pg m)
        (S2114D f g T ptA Pg).square1.toX =
      (S2107ExtLiftToX (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) s).hom ≫
        m.toX ≫
      (S2107ExtLiftToX (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) t).inv :=
  (S2114WP f g T ptA Pg).liftTwoCell_toX W
    (S2107ExtCone (S2114D f g T ptA Pg) s)
    (S2107ExtCone (S2114D f g T ptA Pg) t)
    (S2114ExtConeHom f g T ptA Pg m)

/-- The second available projection equation: along `D.toY1 ; D.toY2`. -/
theorem S2114PastedTwoCell_toY2 {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2114D f g T ptA Pg).square1.Cone W}
    (m : (S2114D f g T ptA Pg).square1.ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2114PastedTwoCell f g T ptA Pg m)
        ((S2114D f g T ptA Pg).square1.toY ≫ (S2114D f g T ptA Pg).toY2) =
      (S2107ExtLiftToY2 (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) s).hom ≫
        (Pseudofunctor.StrongTrans.whiskerRight m.toY
          (S2114D f g T ptA Pg).toY2) ≫
      (S2107ExtLiftToY2 (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) t).inv :=
  (S2114WP f g T ptA Pg).liftTwoCell_toY W
    (S2107ExtCone (S2114D f g T ptA Pg) s)
    (S2107ExtCone (S2114D f g T ptA Pg) t)
    (S2114ExtConeHom f g T ptA Pg m)

/-! ## 3. The exact remaining equation -/

/-- **The exact missing equation family.** -/
def S2114ToYEquation
    (h2 : S1827EssSurjOf (S2114D f g T ptA Pg).square2 (S2114W2 f g T ptA Pg)) : Prop :=
  forall (W : EtaleStackPseudofunctor S1726K)
    (s t : (S2114D f g T ptA Pg).square1.Cone W)
    (m : (S2114D f g T ptA Pg).square1.ConeMorphism s t),
    Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
        (S2114D f g T ptA Pg).square1.toY =
      (S2107ExtLiftToY (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg) h2
        (S2114WP f g T ptA Pg) s).hom ≫
        m.toY ≫
      (S2107ExtLiftToY (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg) h2
        (S2114WP f g T ptA Pg) t).inv

/-- **From a canonical lift 2-cell to the missing equation.** -/
theorem S2114ToYEquation_of_canonicalLift
    (h2 : S1827EssSurjOf (S2114D f g T ptA Pg).square2 (S2114W2 f g T ptA Pg))
    (r : S2107CanonicalLiftTwoCell (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg)
      h2 (S2114WP f g T ptA Pg)) :
    S2114ToYEquation f g T ptA Pg h2 := by
  intro W s t m
  haveI : Subsingleton
      (S2107ExtLift (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) s ⟶
        S2107ExtLift (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) t) :=
    S1897Modification_subsingleton_representable
      (W := W) (T := Pg.pullbackScheme)
      (L := S2107ExtLift (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) s)
      (L' := S2107ExtLift (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) t)
  have hEq : r.liftTwoCell W s t m = S2114PastedTwoCell f g T ptA Pg m :=
    Subsingleton.elim _ _
  have h := r.liftTwoCell_toY W s t m
  rwa [hEq] at h

/-- **From the missing equation to a canonical lift 2-cell.** -/
noncomputable def S2114CanonicalLiftTwoCell_of_toYEquation
    (h2 : S1827EssSurjOf (S2114D f g T ptA Pg).square2 (S2114W2 f g T ptA Pg))
    (h : S2114ToYEquation f g T ptA Pg h2) :
    S2107CanonicalLiftTwoCell (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg)
      h2 (S2114WP f g T ptA Pg) where
  liftTwoCell W s t m := S2114PastedTwoCell f g T ptA Pg m
  liftTwoCell_toX W s t m := S2114PastedTwoCell_toX f g T ptA Pg m
  liftTwoCell_toY W s t m := h W s t m

/-- **The exact reduction at the actual butterfly datum.** -/
theorem S2114CanonicalLiftTwoCell_iff
    (h2 : S1827EssSurjOf (S2114D f g T ptA Pg).square2 (S2114W2 f g T ptA Pg)) :
    Nonempty (S2107CanonicalLiftTwoCell (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg)
      h2 (S2114WP f g T ptA Pg)) ↔
      S2114ToYEquation f g T ptA Pg h2 :=
  ⟨fun ⟨r⟩ => S2114ToYEquation_of_canonicalLift f g T ptA Pg h2 r,
   fun h => ⟨S2114CanonicalLiftTwoCell_of_toYEquation f g T ptA Pg h2 h⟩⟩

/-! ## 4. Assembly of the actual base-change square -/

/-- **The actual butterfly assembly.** -/
noncomputable def S2114ToAWitness_of_canonicalLift
    (h2 : S1827EssSurjOf (S2114D f g T ptA Pg).square2 (S2114W2 f g T ptA Pg))
    (r : S2107CanonicalLiftTwoCell (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg)
      h2 (S2114WP f g T ptA Pg)) :
    (S2086ToASquare f g T ptA Pg).TwoPullbackWitness :=
  S2097SwapWitness (Pg.projectionMap.transformation) (S2086Lift f g T ptA Pg) (ptA) (toA f g)
    ((S2086LiftToA f g T ptA Pg).symm)
    (S2107WitnessOfCanonicalTwoCell (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg)
      h2 (S2114WP f g T ptA Pg) r)

/-- **The actual assembly from the exact missing equation.** -/
noncomputable def S2114ToAWitness_of_toYEquation
    (h2 : S1827EssSurjOf (S2114D f g T ptA Pg).square2 (S2114W2 f g T ptA Pg))
    (h : S2114ToYEquation f g T ptA Pg h2) :
    (S2086ToASquare f g T ptA Pg).TwoPullbackWitness :=
  S2114ToAWitness_of_canonicalLift f g T ptA Pg h2
    (S2114CanonicalLiftTwoCell_of_toYEquation f g T ptA Pg h2 h)

/-- **The precise missing datum on the chosen upper comparison.** -/
def S2114ChosenComparisonCompat
    (h2 : S1827EssSurjOf (S2114D f g T ptA Pg).square2 (S2114W2 f g T ptA Pg)) : Prop :=
  forall (W : EtaleStackPseudofunctor S1726K)
    (s : (S2114D f g T ptA Pg).square1.Cone W),
    Pseudofunctor.StrongTrans.whiskerRight
        (S2107ExtLiftToY (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg) h2
          (S2114WP f g T ptA Pg) s).hom
        (S2114D f g T ptA Pg).xi =
      (S2107LiftToYIsoX (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) s).hom ∧
    Pseudofunctor.StrongTrans.whiskerRight
        (S2107ExtLiftToY (S2114D f g T ptA Pg) (S2114W2 f g T ptA Pg) h2
          (S2114WP f g T ptA Pg) s).hom
        (S2114D f g T ptA Pg).toY2 =
      (S2107LiftToYIsoY (S2114D f g T ptA Pg) (S2114WP f g T ptA Pg) s).hom

/-! ## 5. The standard upper-square inputs, and the canonical twist -/

/-- S1801's forward 2-cell surjectivity for the actual upper square. -/
def S2114UpperTwoCellSurjTo : Prop :=
  S1801TwoCellSurjTo (F := S1726K) (P := sitePseudofunctor f g) (X := A.source.fiber)
    (Y := B.source.fiber) (Z := C.source.fiber)
    (sq := S2076Square (f := f) (g := g)) (S2076Witness (f := f) (g := g))

/-- S1801's backward 2-cell surjectivity for the actual upper square. -/
def S2114UpperTwoCellSurjFrom : Prop :=
  S1801TwoCellSurjFrom (F := S1726K) (P := sitePseudofunctor f g) (X := A.source.fiber)
    (Y := B.source.fiber) (Z := C.source.fiber)
    (sq := S2076Square (f := f) (g := g)) (S2076Witness (f := f) (g := g))

/-- S2099's compatible-lift form for the actual upper square. -/
def S2114UpperCompatibleLift : Prop :=
  forall (W : EtaleStackPseudofunctor S1726K)
    (c : (S2076Square (f := f) (g := g)).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY),
    ∃ e : Iso h ((S2076Witness (f := f) (g := g)).lift W c),
      Pseudofunctor.StrongTrans.whiskerRight e.hom (toA f g) =
          alpha.hom ≫ ((S2076Witness (f := f) (g := g)).liftToX W c).inv ∧
        Pseudofunctor.StrongTrans.whiskerRight e.hom (toB f g) =
          beta.hom ≫ ((S2076Witness (f := f) (g := g)).liftToY W c).inv

/-- S2099's fibre-level twist for the actual upper square. -/
def S2114UpperTwist : Prop :=
  forall (W : EtaleStackPseudofunctor S1726K)
    (c : (S2076Square (f := f) (g := g)).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY),
    S2099Twist f g c h alpha beta

/-- The pointwise form of the twist is the comma-morphism condition (S2099). -/
theorem S2114UpperTwistAt_iff_comma
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2076Square (f := f) (g := g)).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)) :
    S2099TwistAt f g c h alpha beta U x ↔
      ∃ m : (h.app U).toFunctor.obj x ⟶
          (gLiftApp (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) U).obj x,
        m.hom.left = (alpha.hom.as.app U).toNatTrans.app x ∧
          m.hom.right = (beta.hom.as.app U).toNatTrans.app x :=
  S2099TwistAt_iff_comma f g c h alpha beta U x

end Actual

/-! ## 6. Checks and axiom audit -/


#print axioms Coherence.S2114PastedConeCompat
#print axioms Coherence.S2114LowerLiftToACompat
#print axioms S2114ExtConeHom
#print axioms S2114PastedTwoCell_toX
#print axioms S2114PastedTwoCell_toY2
#print axioms S2114ToYEquation_of_canonicalLift
#print axioms S2114CanonicalLiftTwoCell_of_toYEquation
#print axioms S2114CanonicalLiftTwoCell_iff
#print axioms S2114ToAWitness_of_canonicalLift
#print axioms S2114ToAWitness_of_toYEquation
#print axioms S2114UpperTwistAt_iff_comma

end LeanFormal.IUT.XiFPaper.S2114CanonicalLiftTwoCellActual

end