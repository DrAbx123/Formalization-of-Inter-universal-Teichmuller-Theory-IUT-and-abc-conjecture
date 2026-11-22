/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S1841
-/
import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual

/-!
# S1841: affine representability of cover sources at the identity point

## The question, and the geometric argument under test

For a cover `A : S1728Cover = OrbicurveFiniteEtaleCover S1726Orbicurve` the
structure map

    A.map : A.source ⟶ X.stack

is representably finite etale, and `X.stack` is the representable etale stack of
the affine base `S1726AffineOver = Spec R'`.  The intended geometric argument is:

* take the identity point `id : h_{Spec R'} ⟶ X.stack` of the representable base;
* the base change presentation `A.finiteEtale.baseChange S1726AffineOver id`
  produces the affine finite etale scheme `S_A = S1733Model A` and the
  two-commutative square

      h_{S_A} --toSource--> A.source
         |                     |
      projection              A.map
         v                     v
      h_{Spec R'} --id-----> X.stack ;

* since the right leg is an equivalence (the identity), the left leg `toSource`
  should be an equivalence too: pullback of an equivalence is an equivalence.
  Then `A.source` would be represented by the affine finite etale scheme `S_A`,
  giving the affine representation and, with two further inputs, the comparison
  `OrbicurveFiniteEtaleCover X ≌ S1733Slice`.

## What this file proves

1. A general bicategorical lemma, `S1841QuasiEquiv_toY_of_xToBase` and its
   mirror `S1841QuasiEquiv_toX_of_yToBase`: in any two-commutative square that
   carries the **full** 2-dimensional universal property of a two-pullback, the
   pullback of a quasi-equivalence is a quasi-equivalence.  The hypothesis on
   the square is `S1827EssSurjOf`, i.e. essential surjectivity of the cone
   comparison `Hom(W,P) ⟶ Cone(W)`; the recorded `TwoPullbackWitness` supplies
   only the opposite direction (`twoCell_ext`).

2. The application to the actual identity-point square
   (`S1841QuasiEquiv_toSource_of_coneEssSurj`): the geometric argument is valid
   **once the missing half of the 2-dimensional universal property is
   available**.  Concretely, `S1827ConeEssSurj A` gives a quasi-equivalence
   `h_{S_A} ⟶ A.source` whose forward 1-cell is exactly the canonical comparison
   `S1756ToSource A`, hence an affine representation of the cover source
   (`S1841SourceRepresentable_of_coneEssSurj`, `S1841ModelRepresentsSource`).

3. The exact first missing statement is isolated and characterised:
   `S1841FirstMissing` = "for every cover, the identity-point comparison
   `h_{S_A} ⟶ A.source` is a quasi-equivalence", i.e. the source is represented
   by `S_A` itself, and it is equivalent to

   * the full 2-universal property `S1827ConeEssSurj` of the recorded square,
   * `S1831FirstMissing` (apex rigidity),
   * `S1756FirstMissing` (`S1756End A = 1`),
   * `S1756Unit A` (the unit 2-cell `toSource ; lift ≅ 1`),
   * `S1743SourceRetraction`,
   * `S1784LiftPointSurj` (every point of the model comes from the source),
   * `S1831AlgFirstMissing` (the induced endomorphism of the finite etale
     R'-algebra of sections is the identity).

4. The recorded weak witness does **not** imply the missing half: S1801's
   degenerate square has identity right leg, satisfies all seven recorded
   fields, and its cone comparison is not essentially surjective
   (`S1841IdentityLegNotEnough`, re-exported).  So the geometric argument cannot
   be formalised from the recorded fields of
   `EtaleStackBaseChangePresentation`; an input strictly beyond the weak
   `TwoPullbackWitness` is necessary.  This is the honest answer to "does
   representable finite etaleness plus the identity point already give the
   affine representation?": **not from the recorded data**.

5. The conditional bridge, with every remaining input named
   (`S1841CoverSliceEquivalence_of_inputs`,
   `S1841CoverFiniteEtaleEquivalence_of_inputs`): the affine representation of
   every cover source, together with

   * full faithfulness of the canonical S1757 functor (the cover-map comparison,
     S1755/S1812/S1828), and
   * essential surjectivity `S1757EssSurjMissing` (every affine finite etale
     scheme over `Spec R'` is the model of a cover),

   yields S1733's `S1733CoverSliceEquivalence` and the equivalence
   `OrbicurveFiniteEtaleCover S1726Orbicurve ≌ FiniteEtaleCover (Spec R')`
   (`S1814OrbicurveAffineEquivalence`).  The second and third inputs are *not*
   consequences of the first: they are genuine additional geometric/categorical
   content.

## Honest boundary

No `sorry`, no new axiom, no `Shrink`, `ULift` or `PUnit`, and no fake
equivalence or 2-cell.  `S1841FirstMissing` is not inhabited; the
quasi-equivalence of the comparison is only derived from the explicitly named
missing half of the 2-universal property.  The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`; see the `#print axioms` block at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1757SliceFunctorActual
open LeanFormal.IUT.XiFPaper.S1758SourceRetractionActual
open LeanFormal.IUT.XiFPaper.S1781AffineCoverAlgebrasSecondActual
open LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1831StrongSquareGeometricActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

/-! ## 1. Quasi-equivalences of etale stacks over the S1726 field -/

/-- A 1-cell of the bicategory of etale stacks over `S1726K` is a
quasi-equivalence when it has a two-sided inverse up to 2-isomorphism.  This is
the honest 2-categorical notion of equivalence of stacks used throughout the
file. -/
def S1841QuasiEquiv {P Q : EtaleStackPseudofunctor S1726K} (f : P ⟶ Q) : Prop :=
  ∃ inv : Q ⟶ P,
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f inv)
      (Pseudofunctor.StrongTrans.id P)) ∧
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp inv f)
      (Pseudofunctor.StrongTrans.id Q))

/-- The identity 1-cell is a quasi-equivalence. -/
theorem S1841QuasiEquiv_id (P : EtaleStackPseudofunctor S1726K) :
    S1841QuasiEquiv (Pseudofunctor.StrongTrans.id P) :=
  ⟨Pseudofunctor.StrongTrans.id P,
    ⟨S1756LeftUnitorIso (Pseudofunctor.StrongTrans.id P)⟩,
    ⟨S1756LeftUnitorIso (Pseudofunctor.StrongTrans.id P)⟩⟩

/-! ## 2. Pullback of a quasi-equivalence is a quasi-equivalence

The only hypothesis beyond the recorded `TwoPullbackWitness` is the missing half
of the 2-dimensional universal property, `S1827EssSurjOf`: every 1-cell into the
apex whose two projections agree with a cone is 2-isomorphic to the chosen lift
of that cone. -/

/-- The tautological cone over a square: the square itself, read as a cone with
apex its own apex. -/
noncomputable def S1841TautologicalCone {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) : sq.Cone P where
  toX := sq.toX
  toY := sq.toY
  commutes := sq.commutes

/-- **Pullback of a quasi-equivalence (left leg).**  Suppose a two-commutative
square carries the full 2-dimensional universal property of a two-pullback (the
missing essential-surjectivity half supplied by `ess`) and its first leg
`xToBase` is a quasi-equivalence.  Then the second leg `toY` is a
quasi-equivalence.

This is the bicategorical statement underlying the geometric argument: the
pullback of an equivalence along any map is an equivalence.  It is *not* a
consequence of the recorded `TwoPullbackWitness` alone (S1801); it uses `ess`. -/
theorem S1841QuasiEquiv_toY_of_xToBase {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (ess : S1827EssSurjOf sq w)
    (hx : S1841QuasiEquiv sq.xToBase) :
    S1841QuasiEquiv sq.toY := by
  obtain ⟨invX, hu, hc⟩ := hx
  have hunit : Iso (Pseudofunctor.StrongTrans.vcomp sq.xToBase invX)
      (Pseudofunctor.StrongTrans.id X) := hu.some
  have hcounit : Iso (Pseudofunctor.StrongTrans.vcomp invX sq.xToBase)
      (Pseudofunctor.StrongTrans.id Z) := hc.some
  have hcomm : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp sq.yToBase invX) sq.xToBase)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id Y) sq.yToBase) :=
    (S1756AssociatorIso sq.yToBase invX sq.xToBase).trans
      ((S1756WhiskerLeftIso sq.yToBase _ _ hcounit).trans
        ((S1756RightUnitorIso sq.yToBase).trans
          (S1756LeftUnitorIso sq.yToBase).symm))
  let c : sq.Cone Y :=
    { toX := Pseudofunctor.StrongTrans.vcomp sq.yToBase invX
      toY := Pseudofunctor.StrongTrans.id Y
      commutes := hcomm }
  let invY : Y ⟶ P := w.lift Y c
  have hsec : Iso (Pseudofunctor.StrongTrans.vcomp invY sq.toY)
      (Pseudofunctor.StrongTrans.id Y) := w.liftToY Y c
  let cP : sq.Cone P := S1841TautologicalCone sq
  let f : P ⟶ P := Pseudofunctor.StrongTrans.vcomp sq.toY invY
  have hX : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toX) cP.toX) := by
    refine ⟨?_⟩
    have e1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toY invY) sq.toX)
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.vcomp invY sq.toX)) :=
      S1756AssociatorIso sq.toY invY sq.toX
    have e2 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.vcomp invY sq.toX))
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.vcomp sq.yToBase invX)) :=
      S1756WhiskerLeftIso sq.toY _ _ (w.liftToX Y c)
    have e3 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.vcomp sq.yToBase invX))
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toY sq.yToBase) invX) :=
      (S1756AssociatorIso sq.toY sq.yToBase invX).symm
    have e4 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toY sq.yToBase) invX)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toX sq.xToBase) invX) :=
      S1756WhiskerRightIso _ _ invX sq.commutes.symm
    have e5 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toX sq.xToBase) invX)
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.vcomp sq.xToBase invX)) :=
      S1756AssociatorIso sq.toX sq.xToBase invX
    have e6 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.vcomp sq.xToBase invX))
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.id X)) :=
      S1756WhiskerLeftIso sq.toX _ _ hunit
    have e7 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toX (Pseudofunctor.StrongTrans.id X))
        sq.toX :=
      S1756RightUnitorIso sq.toX
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))
  have hY : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toY) cP.toY) := by
    refine ⟨?_⟩
    have e1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toY invY) sq.toY)
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.vcomp invY sq.toY)) :=
      S1756AssociatorIso sq.toY invY sq.toY
    have e2 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.vcomp invY sq.toY))
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.id Y)) :=
      S1756WhiskerLeftIso sq.toY _ _ hsec
    have e3 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toY (Pseudofunctor.StrongTrans.id Y))
        sq.toY :=
      S1756RightUnitorIso sq.toY
    exact e1.trans (e2.trans e3)
  have hLift : Nonempty (Iso f (w.lift P cP)) := ess P cP f hX hY
  have hId : Nonempty (Iso (Pseudofunctor.StrongTrans.id P) (w.lift P cP)) :=
    ess P cP (Pseudofunctor.StrongTrans.id P)
      ⟨S1756LeftUnitorIso sq.toX⟩ ⟨S1756LeftUnitorIso sq.toY⟩
  exact ⟨invY, ⟨hLift.some.trans hId.some.symm⟩, ⟨hsec⟩⟩

/-- **Pullback of a quasi-equivalence (right leg).**  The mirror of
`S1841QuasiEquiv_toY_of_xToBase`: if the second leg `yToBase` is a
quasi-equivalence, then the first leg `toX` is.  This is the form applied to the
identity-point base-change square, whose `yToBase` is the identity of the
representable base. -/
theorem S1841QuasiEquiv_toX_of_yToBase {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (ess : S1827EssSurjOf sq w)
    (hy : S1841QuasiEquiv sq.yToBase) :
    S1841QuasiEquiv sq.toX := by
  obtain ⟨invY, hu, hc⟩ := hy
  have hunit : Iso (Pseudofunctor.StrongTrans.vcomp sq.yToBase invY)
      (Pseudofunctor.StrongTrans.id Y) := hu.some
  have hcounit : Iso (Pseudofunctor.StrongTrans.vcomp invY sq.yToBase)
      (Pseudofunctor.StrongTrans.id Z) := hc.some
  have hcomm : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id X) sq.xToBase)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp sq.xToBase invY) sq.yToBase) :=
    (S1756LeftUnitorIso sq.xToBase).trans
      ((S1756RightUnitorIso sq.xToBase).symm.trans
        ((S1756WhiskerLeftIso sq.xToBase _ _ hcounit.symm).trans
          (S1756AssociatorIso sq.xToBase invY sq.yToBase).symm))
  let c : sq.Cone X :=
    { toX := Pseudofunctor.StrongTrans.id X
      toY := Pseudofunctor.StrongTrans.vcomp sq.xToBase invY
      commutes := hcomm }
  let invX : X ⟶ P := w.lift X c
  have hsec : Iso (Pseudofunctor.StrongTrans.vcomp invX sq.toX)
      (Pseudofunctor.StrongTrans.id X) := w.liftToX X c
  let cP : sq.Cone P := S1841TautologicalCone sq
  let f : P ⟶ P := Pseudofunctor.StrongTrans.vcomp sq.toX invX
  have hX : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toX) cP.toX) := by
    refine ⟨?_⟩
    have e1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toX invX) sq.toX)
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.vcomp invX sq.toX)) :=
      S1756AssociatorIso sq.toX invX sq.toX
    have e2 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.vcomp invX sq.toX))
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.id X)) :=
      S1756WhiskerLeftIso sq.toX _ _ hsec
    have e3 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toX (Pseudofunctor.StrongTrans.id X))
        sq.toX :=
      S1756RightUnitorIso sq.toX
    exact e1.trans (e2.trans e3)
  have hY : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toY) cP.toY) := by
    refine ⟨?_⟩
    have e1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toX invX) sq.toY)
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.vcomp invX sq.toY)) :=
      S1756AssociatorIso sq.toX invX sq.toY
    have e2 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.vcomp invX sq.toY))
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.vcomp sq.xToBase invY)) :=
      S1756WhiskerLeftIso sq.toX _ _ (w.liftToY X c)
    have e3 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toX
          (Pseudofunctor.StrongTrans.vcomp sq.xToBase invY))
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toX sq.xToBase) invY) :=
      (S1756AssociatorIso sq.toX sq.xToBase invY).symm
    have e4 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toX sq.xToBase) invY)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toY sq.yToBase) invY) :=
      S1756WhiskerRightIso _ _ invY sq.commutes
    have e5 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp sq.toY sq.yToBase) invY)
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.vcomp sq.yToBase invY)) :=
      S1756AssociatorIso sq.toY sq.yToBase invY
    have e6 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.vcomp sq.yToBase invY))
        (Pseudofunctor.StrongTrans.vcomp sq.toY
          (Pseudofunctor.StrongTrans.id Y)) :=
      S1756WhiskerLeftIso sq.toY _ _ hunit
    have e7 : Iso
        (Pseudofunctor.StrongTrans.vcomp sq.toY (Pseudofunctor.StrongTrans.id Y))
        sq.toY :=
      S1756RightUnitorIso sq.toY
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))
  have hLift : Nonempty (Iso f (w.lift P cP)) := ess P cP f hX hY
  have hId : Nonempty (Iso (Pseudofunctor.StrongTrans.id P) (w.lift P cP)) :=
    ess P cP (Pseudofunctor.StrongTrans.id P)
      ⟨S1756LeftUnitorIso sq.toX⟩ ⟨S1756LeftUnitorIso sq.toY⟩
  exact ⟨invX, ⟨hLift.some.trans hId.some.symm⟩, ⟨hsec⟩⟩

/-! ## 3. The identity-point base-change square of a cover

The square `S1743Square A` has `xToBase = A.map` and `yToBase = S1733BasePoint`,
and `S1733BasePoint` is the identity 1-cell of the representable base stack. -/

/-- The identity point of the representable base is a quasi-equivalence. -/
theorem S1841BasePoint_quasiEquiv (A : S1728Cover) :
    S1841QuasiEquiv (S1743Square A).yToBase := by
  have hbase : S1841QuasiEquiv S1733BasePoint := by
    refine
      ⟨show S1726Orbicurve.stack.fiber ⟶ S1743Y S1726AffineOver from
          Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver), ?_, ?_⟩
    · exact ⟨show Iso
          (Pseudofunctor.StrongTrans.vcomp S1733BasePoint
            (Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver)))
          (Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver)) from
        S1756LeftUnitorIso (Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver))⟩
    · exact ⟨show Iso
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver)) S1733BasePoint)
          (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber) from
        S1756LeftUnitorIso (Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver))⟩
  exact hbase

/-- The missing half of the 2-universal property of the recorded identity-point
square is exactly what makes the identity-point comparison a quasi-equivalence. -/
theorem S1841QuasiEquiv_toSource_of_coneEssSurj (A : S1728Cover)
    (h : S1827ConeEssSurj A) :
    S1841QuasiEquiv (S1756ToSource A) := by
  have ess : S1827EssSurjOf (S1743Square A) (S1743BaseChange A).isPullback := h
  exact S1841QuasiEquiv_toX_of_yToBase (S1743Square A)
    (S1743BaseChange A).isPullback ess (S1841BasePoint_quasiEquiv A)

/-- Conversely, a quasi-equivalence of the identity-point comparison gives the
full 2-universal property of the recorded square (S1827). -/
theorem S1841ConeEssSurj_of_quasiEquiv (A : S1728Cover)
    (h : S1841QuasiEquiv (S1756ToSource A)) :
    S1827ConeEssSurj A := by
  obtain ⟨inv, hu, hc⟩ := h
  exact S1827ConeEssSurj_of_comparisonQuasiEquiv A
    (show S1827ComparisonQuasiEquiv A from ⟨inv, hu, hc⟩)

/-- **The exact characterisation.**  The canonical identity-point comparison
`h_{S_A} ⟶ A.source` is a quasi-equivalence if and only if the recorded
identity-point base-change square has the full 2-dimensional universal property
(the missing half of the two-pullback property). -/
theorem S1841ConeEssSurj_iff_quasiEquiv (A : S1728Cover) :
    S1827ConeEssSurj A ↔ S1841QuasiEquiv (S1756ToSource A) :=
  ⟨S1841QuasiEquiv_toSource_of_coneEssSurj A, S1841ConeEssSurj_of_quasiEquiv A⟩

/-- The affine representation of a cover source by its identity-point model:
the canonical comparison `h_{S_A} ⟶ A.source` is a quasi-equivalence.  This is
the geometric statement "A.source is represented by S_A". -/
def S1841ModelRepresentsSource (A : S1728Cover) : Prop :=
  S1841QuasiEquiv (S1756ToSource A)

/-- The exact first missing statement, uniformly over the cover type: every
cover source is represented by its identity-point affine finite etale model. -/
def S1841FirstMissing : Prop := ∀ A : S1728Cover, S1841ModelRepresentsSource A

/-- The geometric route, formalized: the missing half of the 2-universal
property gives the affine representation and the stack quasi-equivalence with
`h_{S_A}` as forward 1-cell. -/
theorem S1841GeometricRoute (A : S1728Cover) (h : S1827ConeEssSurj A) :
    S1841ModelRepresentsSource A ∧
      Nonempty (S1756StackEquiv (S1743ModelStack A) (S1743Source A)) := by
  have hq := S1841QuasiEquiv_toSource_of_coneEssSurj A h
  refine ⟨hq, ?_⟩
  obtain ⟨inv, hu, hc⟩ := hq
  exact ⟨{ hom := S1756ToSource A,
           inv := inv,
           unit := hu.some,
           counit := hc.some }⟩

/-- The quasi-equivalence of the canonical comparison packaged as a
`S1756StackEquiv` between the affine model and the cover source. -/
noncomputable def S1841StackEquivOfQuasiEquiv (A : S1728Cover)
    (h : S1841QuasiEquiv (S1756ToSource A)) :
    S1756StackEquiv (S1743ModelStack A) (S1743Source A) where
  hom := S1756ToSource A
  inv := h.choose
  unit := h.choose_spec.1.some
  counit := h.choose_spec.2.some

/-- The missing half of the 2-universal property gives representability of the
cover source by its affine model. -/
theorem S1841SourceRepresentable_of_coneEssSurj (A : S1728Cover)
    (h : S1827ConeEssSurj A) : S1756SourceRepresentable A :=
  ⟨S1841StackEquivOfQuasiEquiv A (S1841QuasiEquiv_toSource_of_coneEssSurj A h)⟩

/-- The affine representation of every cover source from the first missing
statement. -/
theorem S1841SourceRepresentableAll_of_firstMissing (h : S1841FirstMissing) :
    S1756SourceRepresentableAll :=
  fun A => S1841SourceRepresentable_of_coneEssSurj A
    ((S1841ConeEssSurj_iff_quasiEquiv A).mpr (h A))

/-- The first missing statement gives S1756's endomorphism equation. -/
theorem S1841FirstMissing_to_S1756 (h : S1841FirstMissing) : S1756FirstMissing := by
  intro A
  obtain ⟨inv, hu, hc⟩ := h A
  exact (S1827ComparisonQuasiEquiv_iff_end A).mp
    (show S1827ComparisonQuasiEquiv A from ⟨inv, hu, hc⟩)

/-! ## 4. The first missing statement in all recorded forms -/

/-- `S1841FirstMissing` is the full 2-universal property of every recorded
identity-point square (S1827, S1831). -/
theorem S1841FirstMissing_iff_S1827 :
    S1841FirstMissing ↔ S1827FirstMissing := by
  constructor
  · intro h A
    exact (S1841ConeEssSurj_iff_quasiEquiv A).mpr (h A)
  · intro h A
    exact (S1841ConeEssSurj_iff_quasiEquiv A).mp (h A)

/-- `S1841FirstMissing` is exactly S1831's first missing statement. -/
theorem S1841FirstMissing_iff_S1831 :
    S1841FirstMissing ↔ S1831FirstMissing :=
  S1841FirstMissing_iff_S1827.trans S1831FirstMissing_iff_S1827.symm

/-- `S1841FirstMissing` is exactly S1756's endomorphism equation. -/
theorem S1841FirstMissing_iff_S1756 :
    S1841FirstMissing ↔ S1756FirstMissing :=
  S1841FirstMissing_iff_S1827.trans S1827FirstMissing_iff_S1756

/-- `S1841FirstMissing` is exactly S1743's source retraction. -/
theorem S1841FirstMissing_iff_sourceRetraction :
    S1841FirstMissing ↔ S1743SourceRetraction :=
  S1841FirstMissing_iff_S1827.trans S1827FirstMissing_iff_sourceRetraction

/-- `S1841FirstMissing` is exactly the unit 2-cell `toSource ; lift ≅ 1`. -/
theorem S1841FirstMissing_iff_unit :
    S1841FirstMissing ↔ ∀ A : S1728Cover, S1756Unit A := by
  constructor
  · intro h A
    exact (S1756Unit_iff_end A).mpr (S1841FirstMissing_to_S1756 h A)
  · intro h A
    exact S1841QuasiEquiv_toSource_of_coneEssSurj A
      ((S1831StrongSquare_iff_unit A).mpr (h A))

/-- `S1841FirstMissing` is exactly the point-surjectivity form of S1784: every
point of the affine model comes from the source.  This is the most geometric
form of the missing statement which never mentions the self-endomorphism. -/
theorem S1841FirstMissing_iff_liftPointSurj :
    S1841FirstMissing ↔ ∀ A : S1728Cover, S1784LiftPointSurj A :=
  S1841FirstMissing_iff_S1756.trans S1784FirstMissing_iff_liftPointSurj

/-- `S1841FirstMissing` is exactly the finite-etale-algebra form: the induced
endomorphism of the algebra of sections is the identity. -/
theorem S1841FirstMissing_iff_algEnd :
    S1841FirstMissing ↔ ∀ A : S1728Cover, S1831AlgEnd A = 𝟙 (S1781Obj A) :=
  S1841FirstMissing_iff_S1831.trans S1831FirstMissing_iff_algFirstMissing

/-! ## 5. What the recorded weak witness cannot supply

The recorded `TwoPullbackWitness` has the right leg equal to the identity in the
degenerate S1801 square, yet its cone comparison is not essentially surjective.
Hence the geometric argument "the right leg is an identity, so the left leg is
an equivalence" is not derivable from the recorded fields: the missing half of
the 2-universal property is genuinely input, not a coherence condition on
already-given 2-cells.

Neither the stack condition `A.source.isStack` nor the raw finite-etale descent
machinery of S1761 supplies the missing 2-cell: the S1801 countermodel already
satisfies all seven recorded fields with an identity right leg, and the failure
there is the *non-existence* of a 2-cell (S1827WitnessNotIso), not a missing
descent datum.  A genuine proof of `S1841FirstMissing` must therefore use
geometry beyond the recorded fields (e.g. the base-change presentations at the
other scheme points), or the recorded definition of `TwoPullbackWitness` must be
strengthened to the full 2-dimensional universal property. -/

/-- The recorded weak witness does not imply the missing essential surjectivity
of the cone comparison (S1801/S1827, re-exported). -/
theorem S1841RecordedWitnessInsufficient :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor S1726K)
        (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness),
        S1827EssSurjOf sq w) :=
  S1827EssSurjNotFromWitness

/-- The S1801 degenerate square has *identity* right leg and satisfies the full
recorded witness, but its cone comparison is not essentially surjective.  This
is the precise sense in which the recorded fields (and the identity-point
hypothesis) do not suffice at the level of 2-categorical algebra. -/
theorem S1841IdentityLegNotEnough :
    ¬ S1801EssSurjOf S1726K (S1801DegenerateSquare S1726K)
      (S1801DegenerateWitness S1726K) :=
  S1801DegenerateEssSurjFalse S1726K

/-- In the S1801 degenerate square the right leg is literally the identity. -/
theorem S1841DegenerateRightLeg_id :
    (S1801DegenerateSquare S1726K).xToBase =
      Pseudofunctor.StrongTrans.id (S1801PointStack S1726K) := rfl

/-! ## 6. The conditional bridge to the slice and to `FiniteEtaleCover (Spec R')`

The exact first missing statement (`S1841FirstMissing`) supplies the canonical
lift section and hence the canonical S1757 functor; the remaining inputs are
full faithfulness of that functor (the cover-map comparison) and essential
surjectivity (`S1757EssSurjMissing`).  With those three inputs, S1814's
conditional assembly gives both `S1733CoverSliceEquivalence` and the equivalence
`OrbicurveFiniteEtaleCover S1726Orbicurve ≌ FiniteEtaleCover (Spec R')`. -/

/-- The canonical lift section, i.e. the unit 2-cell, from
`S1841FirstMissing`. -/
theorem S1841LiftSection_of_firstMissing (h : S1841FirstMissing) :
    S1757LiftSection :=
  S1814_liftSection_of_firstMissing (S1841FirstMissing_to_S1756 h)

/-- The canonical comparison functor `S1728Cover ⤏ S1733Slice` from
`S1841FirstMissing`. -/
noncomputable def S1841Functor_of_firstMissing (h : S1841FirstMissing) :
    S1728Cover ⥤ S1733Slice :=
  S1757Functor (S1841LiftSection_of_firstMissing h)

/-- **Conditional bridge, affine-slice form.**  `S1841FirstMissing`, full
faithfulness of the canonical functor, and essential surjectivity of the slice
comparison give S1733's cover/slice equivalence. -/
theorem S1841CoverSliceEquivalence_of_inputs (h : S1841FirstMissing)
    (hff : (S1841Functor_of_firstMissing h).FullyFaithful)
    (hess : S1757EssSurjMissing) :
    S1733CoverSliceEquivalence :=
  S1814_sliceEquivalence_of_target
    (S1814_target_of_canonicalData (S1841FirstMissing_to_S1756 h) hff hess)

/-- **Conditional bridge, `FiniteEtaleCover (Spec R')` form.**  The same three
inputs give S1814's target equivalence
`OrbicurveFiniteEtaleCover S1726Orbicurve ≌ FiniteEtaleCover (Spec R')`. -/
theorem S1841CoverFiniteEtaleEquivalence_of_inputs (h : S1841FirstMissing)
    (hff : (S1841Functor_of_firstMissing h).FullyFaithful)
    (hess : S1757EssSurjMissing) :
    S1814OrbicurveAffineEquivalence :=
  S1814_target_of_canonicalData (S1841FirstMissing_to_S1756 h) hff hess

/-- The exact remaining inputs of the affine-slice bridge, named as one
proposition: the affine representation of every cover source, full faithfulness
of the canonical functor, and essential surjectivity.  This is the precise
"first missing" decomposition of S1733's target on the canonical route. -/
structure S1841BridgeInputs where
  /-- The affine representation of every cover source at the identity point. -/
  sourceRepresentation : S1841FirstMissing
  /-- Full faithfulness of the canonical comparison functor. -/
  fullyFaithful :
    (S1841Functor_of_firstMissing sourceRepresentation).FullyFaithful
  /-- Essential surjectivity: every affine finite etale scheme over `Spec R'` is
  the identity-point model of a cover. -/
  essSurj : S1757EssSurjMissing

/-- The three named inputs give the cover/slice equivalence. -/
theorem S1841CoverSliceEquivalence_of_inputs' (d : S1841BridgeInputs) :
    S1733CoverSliceEquivalence :=
  S1841CoverSliceEquivalence_of_inputs d.sourceRepresentation d.fullyFaithful d.essSurj

/-- The three named inputs give the equivalence with `FiniteEtaleCover (Spec R')`. -/
theorem S1841CoverFiniteEtaleEquivalence_of_inputs' (d : S1841BridgeInputs) :
    S1814OrbicurveAffineEquivalence :=
  S1841CoverFiniteEtaleEquivalence_of_inputs d.sourceRepresentation
    d.fullyFaithful d.essSurj


/-! ## 7. Checks and axiom audit -/

#check S1841QuasiEquiv
#check S1841QuasiEquiv_id
#check S1841QuasiEquiv_toY_of_xToBase
#check S1841QuasiEquiv_toX_of_yToBase
#check S1841TautologicalCone
#check S1841BasePoint_quasiEquiv
#check S1841QuasiEquiv_toSource_of_coneEssSurj
#check S1841ConeEssSurj_of_quasiEquiv
#check S1841ConeEssSurj_iff_quasiEquiv
#check S1841ModelRepresentsSource
#check S1841FirstMissing
#check S1841GeometricRoute
#check S1841StackEquivOfQuasiEquiv
#check S1841SourceRepresentable_of_coneEssSurj
#check S1841SourceRepresentableAll_of_firstMissing
#check S1841FirstMissing_to_S1756
#check S1841FirstMissing_iff_S1827
#check S1841FirstMissing_iff_S1831
#check S1841FirstMissing_iff_S1756
#check S1841FirstMissing_iff_sourceRetraction
#check S1841FirstMissing_iff_unit
#check S1841FirstMissing_iff_liftPointSurj
#check S1841FirstMissing_iff_algEnd
#check S1841RecordedWitnessInsufficient
#check S1841IdentityLegNotEnough
#check S1841DegenerateRightLeg_id
#check S1841LiftSection_of_firstMissing
#check S1841Functor_of_firstMissing
#check S1841CoverSliceEquivalence_of_inputs
#check S1841CoverFiniteEtaleEquivalence_of_inputs
#check S1841BridgeInputs
#check S1841CoverSliceEquivalence_of_inputs'
#check S1841CoverFiniteEtaleEquivalence_of_inputs'

#print axioms S1841QuasiEquiv_toY_of_xToBase
#print axioms S1841QuasiEquiv_toX_of_yToBase
#print axioms S1841BasePoint_quasiEquiv
#print axioms S1841QuasiEquiv_toSource_of_coneEssSurj
#print axioms S1841ConeEssSurj_iff_quasiEquiv
#print axioms S1841GeometricRoute
#print axioms S1841SourceRepresentable_of_coneEssSurj
#print axioms S1841FirstMissing_iff_liftPointSurj
#print axioms S1841FirstMissing_iff_algEnd
#print axioms S1841RecordedWitnessInsufficient
#print axioms S1841CoverSliceEquivalence_of_inputs
#print axioms S1841CoverFiniteEtaleEquivalence_of_inputs

end LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
