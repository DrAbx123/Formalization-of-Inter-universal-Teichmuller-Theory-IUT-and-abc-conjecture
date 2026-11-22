import tmp.sheaf.xif.paper.S2010BaseChangeFullActual
import tmp.sheaf.xif.paper.S1804IsoCommaPullbackActual

/-!
# S2015: the corrected full-pullback property and the actual iso-comma fibre

## The repair

S2010 refuted the recorded target

  S1827FirstMissing, S1841FirstMissing, S2007AllBaseChangesFull, S2007FirstMissing

for the recorded definition of EtaleStackBaseChangePresentation: the recorded
field isPullback : (square).TwoPullbackWitness is only the weak seven-field
witness, and the split double cover of the test scheme of the counterexample
cover satisfies it while its apex is not the actual fibre product.

This file defines the corrected property and proves what it yields.

## What is defined

1. S2015IsoCommaObj sq W is the actual iso-comma fibre of a square at a test
   stack W: an object is a pair of 1-cells toX : W -> X, toY : W -> Y
   together with a 2-isomorphism toX ; xToBase ~= toY ; yToBase.
   S2015IsoCommaObjEquiv shows this is exactly the type sq.Cone W of
   pseudo-cones; S2015IsoCommaHom is the matching 1-cell type and is exactly
   sq.ConeMorphism.  S2015IsoCommaComparison is the canonical comparison
   Hom(W,P) -> (iso-comma fibre).

2. S2015FullPullback sq is the full 2-dimensional universal property *on
   1-cells* of the actual iso-comma fibre: every iso-comma object is realised by
   a 1-cell from the apex (exists_lift), and the realising 1-cell is unique up
   to a 2-isomorphism over the cone (unique_lift).  Together with the two-cell
   action and two-cell extensionality already recorded in TwoPullbackWitness,
   this is the full property used by the cancellation/representability argument.
   Functoriality of a chosen lift on cone morphisms is not separately asserted;
   the file proves that this property is exactly the missing half of
   S1827EssSurjOf, i.e. exactly the extra field that S1827/S1841 isolated.

3. S2015FullBaseChangePresentation is EtaleStackBaseChangePresentation with
   the weak witness *strengthened* by isFull : S2015FullPullback square;
   S2015FullFiniteEtale is the corresponding corrected finite-etale predicate.

## What is proved

* S2015FullPullback_iff_essSurj: for a fixed recorded weak witness w, the
  corrected property is exactly the missing half S1827EssSurjOf sq w
  (essential surjectivity of the cone comparison).  This is the precise sense in
  which the repair strengthens *only* the missing field, and in which the
  corrected property is the full pullback property on 1-cells.

* S2015IdentityFull_iff_coneEssSurj: at the identity point of a cover, the
  corrected property of the recorded square is exactly the old
  S1827ConeEssSurj; hence it is equivalent to representability of the cover
  source by its affine model (S1841ConeEssSurj_iff_quasiEquiv).

* S2015IdentityFull_iff_sourceRepresentable: the corrected property of the
  recorded identity-point square is equivalent to a quasi-equivalence of
  S1756ToSource, i.e. to the source being represented by the affine model.

* S2015CoverFiberDiscrete_of_identityRepair: a corrected (actual iso-comma)
  presentation at the identity point of a cover yields a genuine quasi-equivalence
  Y Q -> C.source (by S1841QuasiEquiv_toX_of_yToBase, whose right leg is the
  identity point), hence representability of the source and discreteness of every
  fibre, S2001CoverFiberDiscrete C.

* S2015UniqFirstMissing_of_identityRepairAll: consequently, the corrected
  presentations at the identity point (for all covers) imply S2001UniqFirstMissing.

* S2015_not_fullOfWitness and S2015_not_recordedFullAll: the corrected
  property is *not* a consequence of the recorded weak witnesses, and the
  uniform statement "every recorded presentation is the actual pullback" is
  false (S2010).  Hence the repair must be existential: the corrected finite-etale
  structure is data, not a property of the recorded weak witness.

## Exact first missing after the repair

  S2015IdentityRepairAll : forall C, Nonempty (S2015FullBaseChangePresentation
      C.map S1726AffineOver S1733BasePoint)

i.e. every finite-etale cover admits, at the canonical identity point, a
base-change presentation whose apex is the actual iso-comma fibre.  This is the
geometric input (representability of the finite-etale map by its actual fibre
product, plus the finite-etale projection) that the recorded weak data do not
supply.  It is sufficient for S2001UniqFirstMissing, and it is not refuted by
S2010 (the corrected property is not vacuous: it holds for every actual pullback
square, see S2015FullPullback_sourceSquare).  This file does not construct that
presentation for an arbitrary cover; doing so is the remaining geometric
theorem, and it is recorded as the named first missing above.  In particular
S2015IdentityRepairAll is implied by the old first missing
(S2015IdentityRepairAll_of_firstMissing) and by the corrected all-points data
(S2015IdentityRepairAll_of_correctedRepair), while the uniform *recorded* version
is false (S2015_not_recordedFullAll) and the recorded identity-point square of
S2010's counterexample is not full (S2015_not_full_counterexample).  Sufficiency
for S2001UniqFirstMissing is proved; necessity is not claimed.

## Honest boundary

No sorry, no new axiom, no Shrink/ULift/PUnit, no fake 2-cell and no fake
equivalence.  The corrected structures are definitions; the theorems are proved
from them together with the existing tree (S1841, S2007, S2010).  The only
axioms used are propext, Classical.choice and Quot.sound.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2015FullPullbackActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual
open LeanFormal.IUT.XiFPaper.S2007CoverFiberDiscreteActual
open LeanFormal.IUT.XiFPaper.S2010BaseChangeFullActual

/-! ## 1. The actual iso-comma fibre of a square -/

/-- The actual iso-comma fibre of a 2-commutative square at a test stack W:
an object is a pair of 1-cells into the two legs together with a 2-isomorphism
between their images in the common target.  This is the object type of the
homotopy fibre product Hom(W,X) x^h_{Hom(W,Z)} Hom(W,Y). -/
structure S2015IsoCommaObj {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (W : EtaleStackPseudofunctor S1726K) where
  /-- The 1-cell into the first leg. -/
  toX : Pseudofunctor.StrongTrans W X
  /-- The 1-cell into the second leg. -/
  toY : Pseudofunctor.StrongTrans W Y
  /-- The 2-isomorphism making the pair commute up to coherent 2-cells. -/
  iso : Iso (Pseudofunctor.StrongTrans.vcomp toX sq.xToBase)
    (Pseudofunctor.StrongTrans.vcomp toY sq.yToBase)

/-- The iso-comma fibre is definitionally the type of pseudo-cones. -/
noncomputable def S2015IsoCommaObjEquiv {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (W : EtaleStackPseudofunctor S1726K) :
    S2015IsoCommaObj sq W ≃ sq.Cone W where
  toFun c := { toX := c.toX, toY := c.toY, commutes := c.iso }
  invFun c := { toX := c.toX, toY := c.toY, iso := c.commutes }
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

/-- A 1-cell of the actual iso-comma fibre: a pair of 2-cells compatible with
the two squares.  This is exactly ConeMorphism. -/
structure S2015IsoCommaHom {P X Y Z : EtaleStackPseudofunctor S1726K}
    {sq : EtalePseudofunctorSquare P X Y Z} {W : EtaleStackPseudofunctor S1726K}
    (c1 c2 : S2015IsoCommaObj sq W) where
  /-- The 2-cell on the first projection. -/
  toX : c1.toX ⟶ c2.toX
  /-- The 2-cell on the second projection. -/
  toY : c1.toY ⟶ c2.toY
  /-- The compatibility square of the two 2-cells. -/
  compatibility :
    Pseudofunctor.StrongTrans.whiskerRight toX sq.xToBase ≫ c2.iso.hom =
      c1.iso.hom ≫ Pseudofunctor.StrongTrans.whiskerRight toY sq.yToBase

/-- The 1-cells of the iso-comma fibre are exactly the cone morphisms. -/
noncomputable def S2015IsoCommaHomEquiv {P X Y Z : EtaleStackPseudofunctor S1726K}
    {sq : EtalePseudofunctorSquare P X Y Z} {W : EtaleStackPseudofunctor S1726K}
    (c1 c2 : S2015IsoCommaObj sq W) :
    S2015IsoCommaHom c1 c2 ≃
      sq.ConeMorphism (S2015IsoCommaObjEquiv sq W c1)
        (S2015IsoCommaObjEquiv sq W c2) where
  toFun m := { toX := m.toX, toY := m.toY, compatibility := m.compatibility }
  invFun m := { toX := m.toX, toY := m.toY, compatibility := m.compatibility }
  left_inv m := by cases m; rfl
  right_inv m := by cases m; rfl

/-- The canonical comparison of the apex with the actual iso-comma fibre:
a 1-cell f : W -> P is sent to the pair of its composites with the two legs,
made commutative by the 2-cell of the square. -/
noncomputable def S2015IsoCommaComparison {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (W : EtaleStackPseudofunctor S1726K)
    (f : Pseudofunctor.StrongTrans W P) : S2015IsoCommaObj sq W where
  toX := Pseudofunctor.StrongTrans.vcomp f sq.toX
  toY := Pseudofunctor.StrongTrans.vcomp f sq.toY
  iso := (S1756AssociatorIso f sq.toX sq.xToBase).trans
    ((S1756WhiskerLeftIso f _ _ sq.commutes).trans
      (S1756AssociatorIso f sq.toY sq.yToBase).symm)

/-! ## 2. The corrected full pullback property -/

/-- The full 2-dimensional universal property of the actual iso-comma fibre, on
1-cells.  Every iso-comma object is realised by a 1-cell from the apex, and the
realising 1-cell is unique up to a 2-isomorphism over the given cone.  With the
2-cell action (liftTwoCell) and 2-cell extensionality (twoCell_ext) already
recorded in TwoPullbackWitness, this is the full property of the fibre product
used below.  S2015FullPullback_iff_essSurj shows that it is exactly the half
missing from the weak seven-field witness. -/
structure S2015FullPullback {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) : Prop where
  /-- Essential surjectivity of the comparison with the iso-comma fibre. -/
  exists_lift :
    ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
      ∃ f : Pseudofunctor.StrongTrans W P,
        Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toX) c.toX) ∧
          Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toY) c.toY)
  /-- Uniqueness, up to 2-isomorphism, of the realisation of a cone. -/
  unique_lift :
    ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W)
      (f g : Pseudofunctor.StrongTrans W P),
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toX) c.toX) →
        Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toY) c.toY) →
          Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp g sq.toX) c.toX) →
            Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp g sq.toY) c.toY) →
              Nonempty (Iso f g)

/-- The corrected property is exactly the missing half.  Relative to any
recorded weak witness w, S2015FullPullback sq holds if and only if the cone
comparison is essentially surjective (S1827EssSurjOf sq w).  Thus the repair
adds exactly the field that S1827/S1841 isolated, and no more. -/
theorem S2015FullPullback_iff_essSurj {P X Y Z : EtaleStackPseudofunctor S1726K}
    {sq : EtalePseudofunctorSquare P X Y Z} (w : sq.TwoPullbackWitness) :
    S2015FullPullback sq ↔ S1827EssSurjOf sq w := by
  constructor
  · intro h W c f hX hY
    exact h.unique_lift W c f (w.lift W c) hX hY
      ⟨w.liftToX W c⟩ ⟨w.liftToY W c⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro W c
      exact ⟨w.lift W c, ⟨⟨w.liftToX W c⟩, ⟨w.liftToY W c⟩⟩⟩
    · intro W c f g hXf hYf hXg hYg
      exact ⟨(h W c f hXf hYf).some.trans (h W c g hXg hYg).some.symm⟩

/-! ## 3. The corrected base-change presentation and finite-etale predicate -/

/-- The corrected base-change presentation: the recorded weak witness is kept,
and the square is moreover required to satisfy the full iso-comma universal
property on 1-cells.  This is the literal strengthening of
EtaleStackBaseChangePresentation.isPullback : TwoPullbackWitness by the missing
half (essential surjectivity and uniqueness of the iso-comma comparison). -/
structure S2015FullBaseChangePresentation
    {source target : EtaleStackOverField S1726K}
    (map : source.Hom target)
    (testScheme : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber) where
  /-- The scheme presenting the actual fibre product. -/
  pullbackScheme : SchemeOverField S1726K
  /-- The projection to the test scheme. -/
  projection : pullbackScheme ⟶ testScheme
  /-- The projection is induced by the actual scheme morphism. -/
  projectionMap : SchemeRepresentableMap projection
  /-- The comparison to the source. -/
  toSource : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K pullbackScheme) source.fiber
  /-- The 2-commutativity of the square. -/
  commutes : Iso
    (Pseudofunctor.StrongTrans.vcomp toSource map)
    (Pseudofunctor.StrongTrans.vcomp projectionMap.transformation point)
  /-- The recorded weak witness (retained for compatibility with the tree). -/
  isPullback :
    (EtalePseudofunctorSquare.mk toSource projectionMap.transformation map point
      commutes).TwoPullbackWitness
  /-- The corrected full property: the apex is the actual iso-comma fibre. -/
  isFull :
    S2015FullPullback
      (EtalePseudofunctorSquare.mk toSource projectionMap.transformation map point
        commutes)

/-- The square underlying a corrected presentation. -/
noncomputable def S2015FullBaseChangePresentation.square
    {source target : EtaleStackOverField S1726K}
    {map : source.Hom target}
    {testScheme : SchemeOverField S1726K}
    {point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber}
    (P : S2015FullBaseChangePresentation map testScheme point) :
    EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor S1726K P.pullbackScheme)
      source.fiber
      (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber :=
  EtalePseudofunctorSquare.mk P.toSource P.projectionMap.transformation map point
    P.commutes

/-- The full property is the property of the square of the presentation. -/
theorem S2015FullBaseChangePresentation.isFull_square
    {source target : EtaleStackOverField S1726K}
    {map : source.Hom target}
    {testScheme : SchemeOverField S1726K}
    {point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber}
    (P : S2015FullBaseChangePresentation map testScheme point) :
    S2015FullPullback P.square :=
  P.isFull

/-- The corrected presentation has the missing essential-surjectivity half. -/
theorem S2015FullBaseChangePresentation.essSurj
    {source target : EtaleStackOverField S1726K}
    {map : source.Hom target}
    {testScheme : SchemeOverField S1726K}
    {point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber}
    (P : S2015FullBaseChangePresentation map testScheme point) :
    S1827EssSurjOf P.square P.isPullback :=
  (S2015FullPullback_iff_essSurj P.isPullback).mp P.isFull

/-- Forgetting the corrected full property gives the recorded presentation. -/
noncomputable def S2015FullBaseChangePresentation.toRecorded
    {source target : EtaleStackOverField S1726K}
    {map : source.Hom target}
    {testScheme : SchemeOverField S1726K}
    {point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber}
    (P : S2015FullBaseChangePresentation map testScheme point) :
    EtaleStackBaseChangePresentation map testScheme point where
  pullbackScheme := P.pullbackScheme
  projection := P.projection
  projectionMap := P.projectionMap
  toSource := P.toSource
  commutes := P.commutes
  isPullback := P.isPullback

/-- The corrected finite-etale predicate: every scheme-valued point admits an
actual iso-comma base-change presentation whose projection is finite etale. -/
structure S2015FullFiniteEtale {source target : EtaleStackOverField S1726K}
    (map : source.Hom target) where
  /-- The corrected base-change presentation at every scheme-valued point. -/
  baseChange :
    ∀ (testScheme : SchemeOverField S1726K)
      (point : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber),
      S2015FullBaseChangePresentation map testScheme point
  /-- The projections are finite etale. -/
  hasProperty :
    ∀ (testScheme : SchemeOverField S1726K)
      (point : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber),
      IsFinite (baseChange testScheme point).projection.left ∧
        Etale (baseChange testScheme point).projection.left

/-- A corrected finite-etale map is, in particular, a recorded finite-etale map. -/
noncomputable def S2015FullFiniteEtale.toRecorded
    {source target : EtaleStackOverField S1726K}
    {map : source.Hom target}
    (fe : S2015FullFiniteEtale map) :
    EtaleStackFiniteEtaleMorphism map where
  baseChange testScheme point := (fe.baseChange testScheme point).toRecorded
  hasProperty testScheme point := fe.hasProperty testScheme point
/-! ## 4. The corrected property at the identity point -/

/-- At the identity point, the corrected property of the recorded square is
exactly the old missing half. -/
theorem S2015IdentityFull_iff_coneEssSurj (C : S1728Cover) :
    S2015FullPullback (S1743Square C) ↔ S1827ConeEssSurj C :=
  S2015FullPullback_iff_essSurj (S1743BaseChange C).isPullback

/-- The corrected property of the recorded identity-point square is equivalent to
a quasi-equivalence of the canonical comparison, i.e. to representability of the
cover source by its affine model. -/
theorem S2015IdentityFull_iff_sourceRepresentable (C : S1728Cover) :
    S2015FullPullback (S1743Square C) ↔
      S1841QuasiEquiv (S1756ToSource C) :=
  (S2015IdentityFull_iff_coneEssSurj C).trans
    (S1841ConeEssSurj_iff_quasiEquiv C)

/-- Conversely, source representability gives the corrected property of the
recorded square. -/
theorem S2015IdentityFull_of_sourceRepresentable (C : S1728Cover)
    (h : S1841QuasiEquiv (S1756ToSource C)) :
    S2015FullPullback (S1743Square C) :=
  (S2015IdentityFull_iff_sourceRepresentable C).mpr h

/-! ## 5. Consequences: cover-fibre discreteness and uniq -/

/-- The source is represented by the actual pullback scheme of a corrected
identity-point presentation. -/
def S2015SourceRepresentedBy (C : S1728Cover)
    (Q : SchemeOverField S1726K) : Prop :=
  Nonempty (S1756StackEquiv (S1743Y Q) C.source.fiber)

/-- A corrected identity-point presentation gives representability of the
cover source by its own (corrected) pullback scheme.  The square of P has right
leg the identity point, so the full 2-universal property makes its first leg a
quasi-equivalence (S1841QuasiEquiv_toX_of_yToBase). -/
theorem S2015SourceRepresentedBy_of_identityRepair (C : S1728Cover)
    (P : S2015FullBaseChangePresentation C.map S1726AffineOver S1733BasePoint) :
    S2015SourceRepresentedBy C P.pullbackScheme := by
  have hq : S1841QuasiEquiv P.square.toX :=
    S1841QuasiEquiv_toX_of_yToBase P.square P.isPullback P.essSurj
      (S1841BasePoint_quasiEquiv C)
  exact ⟨{ hom := P.toSource
           inv := hq.choose
           unit := hq.choose_spec.1.some
           counit := hq.choose_spec.2.some }⟩

/-- A corrected identity-point presentation gives discreteness of every
fibre of the cover source.  The apex is representable, and the comparison with
it is a quasi-equivalence; S2007 transfers subsingleton hom types along the
resulting stack equivalence. -/
theorem S2015CoverFiberDiscrete_of_identityRepair (C : S1728Cover)
    (P : S2015FullBaseChangePresentation C.map S1726AffineOver S1733BasePoint) :
    S2001CoverFiberDiscrete C := by
  have hq : S1841QuasiEquiv P.square.toX :=
    S1841QuasiEquiv_toX_of_yToBase P.square P.isPullback P.essSurj
      (S1841BasePoint_quasiEquiv C)
  exact S2007Subsingleton_of_stackEquiv
    { hom := P.toSource
      inv := hq.choose
      unit := hq.choose_spec.1.some
      counit := hq.choose_spec.2.some }
    (fun U X Y => S2007RepresentableFiberSubsingleton P.pullbackScheme U X Y)

/-- The corrected property of a full finite-etale structure gives discreteness
of the fibres of the source. -/
theorem S2015CoverFiberDiscrete_of_fullFiniteEtale (C : S1728Cover)
    (fe : S2015FullFiniteEtale C.map) : S2001CoverFiberDiscrete C :=
  S2015CoverFiberDiscrete_of_identityRepair C
    (fe.baseChange S1726AffineOver S1733BasePoint)

/-- The corrected presentations at the identity point, for every cover.  This is
the exact first missing statement after the repair. -/
def S2015IdentityRepair (C : S1728Cover) : Prop :=
  Nonempty (S2015FullBaseChangePresentation C.map S1726AffineOver S1733BasePoint)

/-- The corrected identity-point presentations, uniformly over all covers. -/
def S2015IdentityRepairAll : Prop := ∀ C : S1728Cover, S2015IdentityRepair C

/-- The corrected full finite-etale data, uniformly over all covers. -/
def S2015CorrectedRepair : Prop :=
  ∀ C : S1728Cover, Nonempty (S2015FullFiniteEtale C.map)

/-- The corrected uniform input gives S2001UniqFirstMissing. -/
theorem S2015UniqFirstMissing_of_identityRepairAll
    (h : S2015IdentityRepairAll) : S2001UniqFirstMissing :=
  fun C => S2015CoverFiberDiscrete_of_identityRepair C (h C).some

/-- The all-points corrected finite-etale data gives the same conclusion. -/
theorem S2015UniqFirstMissing_of_correctedRepair
    (h : S2015CorrectedRepair) : S2001UniqFirstMissing :=
  fun C => S2015CoverFiberDiscrete_of_fullFiniteEtale C (h C).some

/-! ## 5b. The corrected first missing and the old first missing -/

/-- If the recorded identity-point square is the actual iso-comma pullback, the
recorded presentation itself is a corrected presentation. -/
noncomputable def S2015FullBaseChangePresentation.ofRecorded (C : S1728Cover)
    (h : S2015FullPullback (S1743Square C)) :
    S2015FullBaseChangePresentation C.map S1726AffineOver S1733BasePoint where
  pullbackScheme := (S1743BaseChange C).pullbackScheme
  projection := (S1743BaseChange C).projection
  projectionMap := (S1743BaseChange C).projectionMap
  toSource := (S1743BaseChange C).toSource
  commutes := (S1743BaseChange C).commutes
  isPullback := (S1743BaseChange C).isPullback
  isFull := h

/-- The corrected all-points data refines the corrected identity-point data. -/
theorem S2015IdentityRepairAll_of_correctedRepair
    (h : S2015CorrectedRepair) : S2015IdentityRepairAll :=
  fun C => ⟨(h C).some.baseChange S1726AffineOver S1733BasePoint⟩

/-- The old first missing (source representability by the recorded affine
model) implies the corrected identity-point presentations.  Since the recorded
model is then the actual fibre product, the recorded weak witness is upgraded by
the corrected full property. -/
theorem S2015IdentityRepairAll_of_firstMissing (h : S1841FirstMissing) :
    S2015IdentityRepairAll :=
  fun C => ⟨S2015FullBaseChangePresentation.ofRecorded C
    ((S2015IdentityFull_iff_coneEssSurj C).mpr
      ((S1841ConeEssSurj_iff_quasiEquiv C).mpr (h C)))⟩

/-! ## 6. The repair is genuine: the recorded version is false -/

/-- The uniform statement that every recorded presentation is the actual
iso-comma pullback. -/
def S2015RecordedFullAll : Prop :=
  ∀ C : S1728Cover, S2015FullPullback (S1743Square C)

/-- The uniform recorded version is exactly the old (refuted) target. -/
theorem S2015RecordedFullAll_iff_firstMissing :
    S2015RecordedFullAll ↔ S1827FirstMissing :=
  forall_congr' (fun C => S2015IdentityFull_iff_coneEssSurj C)

/-- The uniform recorded version is false: S2010's counterexample cover has a
recorded weak witness whose cone comparison is not essentially surjective. -/
theorem S2015_not_recordedFullAll : ¬ S2015RecordedFullAll :=
  fun h => S2010_not_S1827FirstMissing
    ((S2015RecordedFullAll_iff_firstMissing).mp h)

/-- The recorded identity-point square of S2010's counterexample cover is not
the actual iso-comma pullback. -/
theorem S2015_not_full_counterexample :
    ¬ S2015FullPullback (S1743Square S2010CounterCover) :=
  fun h => S2010Counter_not_coneEssSurj
    ((S2015IdentityFull_iff_coneEssSurj S2010CounterCover).mp h)

/-- The corrected property is not implied by the recorded weak witnesses in
general. -/
theorem S2015_not_fullOfWitness :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor S1726K)
        (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness),
        S2015FullPullback sq) := by
  intro h
  exact S2010_not_S1827FirstMissing (fun C =>
    (S2015IdentityFull_iff_coneEssSurj C).mp
      (h (S1743ModelStack C) (S1743Source C) (S1743Y S1726AffineOver)
        S1726Orbicurve.stack.fiber (S1743Square C) (S1743BaseChange C).isPullback))

/-- The corrected property is not vacuous: the actual pullback square of
(A.map, id) (apex the source itself, S1804) satisfies it. -/
theorem S2015FullPullback_sourceSquare (A : S1728Cover) :
    S2015FullPullback (S1804SourceSquare A) := by
  refine ⟨?_, ?_⟩
  · intro W c
    refine ⟨c.toX, ⟨⟨S1756RightUnitorIso c.toX⟩, ?_⟩⟩
    exact ⟨c.commutes.trans (S1756RightUnitorIso c.toY)⟩
  · intro W c f g hXf hYf hXg hYg
    obtain ⟨eXf⟩ := hXf
    obtain ⟨eXg⟩ := hXg
    exact ⟨(S1756RightUnitorIso f).symm.trans
      (eXf.trans (eXg.symm.trans (S1756RightUnitorIso g)))⟩

/-! ## 7. Checks and axiom audit -/

#check S2015IsoCommaObj
#check S2015IsoCommaObjEquiv
#check S2015IsoCommaHom
#check S2015IsoCommaHomEquiv
#check S2015IsoCommaComparison
#check S2015FullPullback
#check S2015FullPullback_iff_essSurj
#check S2015FullBaseChangePresentation
#check S2015FullBaseChangePresentation.square
#check S2015FullBaseChangePresentation.essSurj
#check S2015FullBaseChangePresentation.toRecorded
#check S2015FullFiniteEtale
#check S2015FullFiniteEtale.toRecorded
#check S2015IdentityFull_iff_coneEssSurj
#check S2015IdentityFull_iff_sourceRepresentable
#check S2015SourceRepresentedBy
#check S2015SourceRepresentedBy_of_identityRepair
#check S2015CoverFiberDiscrete_of_identityRepair
#check S2015CoverFiberDiscrete_of_fullFiniteEtale
#check S2015IdentityRepair
#check S2015IdentityRepairAll
#check S2015CorrectedRepair
#check S2015UniqFirstMissing_of_identityRepairAll
#check S2015UniqFirstMissing_of_correctedRepair
#check S2015FullBaseChangePresentation.ofRecorded
#check S2015IdentityRepairAll_of_correctedRepair
#check S2015IdentityRepairAll_of_firstMissing
#check S2015_not_full_counterexample
#check S2015RecordedFullAll
#check S2015RecordedFullAll_iff_firstMissing
#check S2015_not_recordedFullAll
#check S2015_not_fullOfWitness
#check S2015FullPullback_sourceSquare

#print axioms S2015IsoCommaObjEquiv
#print axioms S2015IsoCommaHomEquiv
#print axioms S2015FullPullback_iff_essSurj
#print axioms S2015FullBaseChangePresentation.essSurj
#print axioms S2015FullBaseChangePresentation.toRecorded
#print axioms S2015FullFiniteEtale.toRecorded
#print axioms S2015IdentityFull_iff_coneEssSurj
#print axioms S2015IdentityFull_iff_sourceRepresentable
#print axioms S2015SourceRepresentedBy_of_identityRepair
#print axioms S2015CoverFiberDiscrete_of_identityRepair
#print axioms S2015CoverFiberDiscrete_of_fullFiniteEtale
#print axioms S2015UniqFirstMissing_of_identityRepairAll
#print axioms S2015UniqFirstMissing_of_correctedRepair
#print axioms S2015FullBaseChangePresentation.ofRecorded
#print axioms S2015IdentityRepairAll_of_correctedRepair
#print axioms S2015IdentityRepairAll_of_firstMissing
#print axioms S2015_not_full_counterexample
#print axioms S2015RecordedFullAll_iff_firstMissing
#print axioms S2015_not_recordedFullAll
#print axioms S2015_not_fullOfWitness
#print axioms S2015FullPullback_sourceSquare

end LeanFormal.IUT.XiFPaper.S2015FullPullbackActual
