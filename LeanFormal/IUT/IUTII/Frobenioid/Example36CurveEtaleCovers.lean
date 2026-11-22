import Mathlib.AlgebraicGeometry.Pullbacks
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.Tactic

/-!
# Foundation F3b: finite etale covers of the actual curve and punctured curve

Source anchor: IUT I/II, the D6 curve-Pi input; foundation item F3b.  This file
instantiates the actual finite etale cover category of the ONCE-punctured source
curve curveScheme K = E \ {O} and of the TWO-punctured EXTRA open subscheme
curveTwoPuncturedScheme K = E \ {O,P} (this extra object is not the source)
constructed in Example36CurveScheme.lean, proves basic actual facts about it,
connects affine covers to finite etale coordinate-ring algebras, and freezes the
exact remaining Galois/geometric-connectedness/fiber/pi-1 card.  No fake cover
category is introduced.

## Content

* curveAffineEtaleCovers K is the actual category FiniteEtaleCover (curveScheme K)
  of finite etale covers of the ONCE-punctured source E \ {O}; this is restated as
  curveOncePuncturedEtaleCovers K.  curveTwoPuncturedEtaleCovers K is the
  corresponding category for the TWO-punctured extra open subscheme E \ {O,P}.  Both are instances
  of the foundations FiniteEtaleCover full subcategory of Over of the base.
* The terminal cover candidates curveAffineTerminalCover (once-punctured source)
  and curveTwoPuncturedTerminalCover (two-punctured extra) are constructed from
  the identity morphism; their structure maps are the identity and hence finite
  and etale (instances).
* Actual pullback functors: pullback of covers along the open immersion
  curveTwoPuncturedOpenMap (curveTwoPuncturedOpenPullback), along the punctured
  structure morphism to Spec K (curveTwoPuncturedStructurePullback), and along the
  affine structure morphism to Spec K (curveAffineStructurePullback).  These use
  the foundations FiniteEtaleCover.pullback and the pullback instances for
  schemes.
* Actual algebra covers: for a commutative ring R and a finite etale R-algebra A
  (CommAlgCat.FiniteEtale R), the structure morphism Spec A -> Spec R is finite
  and etale, giving an actual finite etale cover of Spec R
  (finiteEtaleAlgebraCoverOf).  Applied to the coordinate ring
  curveCoordinateRing K, this gives actual finite etale covers of the affine
  curve from finite etale coordinate-ring algebras
  (curveCoordinateAlgebraCover).  The proofs use the Spec/ring-hom property
  comparisons, not a card.
* Frozen card SchemeGaloisConnectednessCard (and its specializations
  curveTwoPuncturedGaloisConnectednessCard): the exact missing geometric
  connectedness, Galois category structure, fiber functor and curve pi-1.  The
  card is DATA with no inhabitant and no consumer.

## Honest boundary

The terminal cover objects are constructed but their full universal property
(IsTerminal) and finite coproducts in the cover category are not formalized
here; this is recorded as remaining basic work, not hidden by a card.  No fake
Galois category, no fake fiber functor and no card-only substitute for the
actual covers and pullbacks are used.  No theta / q-pilot / Tate claim is made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open AlgebraicGeometry CategoryTheory
open EtaleCoverFoundations

universe u

/-! ## 1. The cover categories of the curve and the punctured curve -/

/-- The actual category of finite etale covers of the affine Weierstrass curve
scheme y^2 = x^3 - x. -/
abbrev curveAffineEtaleCovers (K : Type u) [Field K] : Type (u + 1) :=
  FiniteEtaleCover (curveScheme K)

/-- The actual category of finite etale covers of the once-punctured curve. -/
abbrev curveTwoPuncturedEtaleCovers (K : Type u) [Field K] : Type (u + 1) :=
  FiniteEtaleCover (curveTwoPuncturedScheme K)

/-- The actual open immersion of the punctured curve into the affine curve,
which is the base change direction for covers. -/
abbrev curveTwoPuncturedCoverBaseMap (K : Type u) [Field K] :
    curveTwoPuncturedScheme K ⟶ curveScheme K :=
  curveTwoPuncturedOpenMap K

/-! ## 2. Terminal cover candidates and basic finite/etale facts -/

/-- The terminal cover candidate of a scheme S: the identity cover. -/
abbrev terminalCover (S : Scheme) : FiniteEtaleCover S :=
  FiniteEtaleCover.mk (𝟙 S) inferInstance inferInstance

/-- The identity cover is a finite etale cover: its structure map is the
identity, which is etale and finite (actual instances). -/
theorem terminalCover_etale_finite (S : Scheme) :
    Etale (terminalCover S).obj.hom ∧ IsFinite (terminalCover S).obj.hom :=
  ⟨FiniteEtaleCover.etale_structureMap (terminalCover S),
    FiniteEtaleCover.finite_structureMap (terminalCover S)⟩

/-- The terminal cover candidate of the affine curve. -/
abbrev curveAffineTerminalCover (K : Type u) [Field K] :
    curveAffineEtaleCovers K :=
  terminalCover (curveScheme K)

/-- The terminal cover candidate of the punctured curve. -/
abbrev curveTwoPuncturedTerminalCover (K : Type u) [Field K] :
    curveTwoPuncturedEtaleCovers K :=
  terminalCover (curveTwoPuncturedScheme K)

/-- Basic actual fact: the structure map of every object of the affine cover
category to the curve is etale and finite. -/
theorem curveAffineEtaleCover_structureMap_finite_etale
    (K : Type u) [Field K] (C : curveAffineEtaleCovers K) :
    Etale (FiniteEtaleCover.structureMap C) ∧
      IsFinite (FiniteEtaleCover.structureMap C) :=
  ⟨FiniteEtaleCover.etale_structureMap C, FiniteEtaleCover.finite_structureMap C⟩

/-- Basic actual fact: the structure map of every object of the punctured cover
category to the punctured curve is etale and finite. -/
theorem curveTwoPuncturedEtaleCover_structureMap_finite_etale
    (K : Type u) [Field K] (C : curveTwoPuncturedEtaleCovers K) :
    Etale (FiniteEtaleCover.structureMap C) ∧
      IsFinite (FiniteEtaleCover.structureMap C) :=
  ⟨FiniteEtaleCover.etale_structureMap C, FiniteEtaleCover.finite_structureMap C⟩

/-! ## 3. Actual pullback functors -/

/-- Pullback of finite etale covers of the affine curve along the open
immersion of the punctured curve. -/
abbrev curveTwoPuncturedOpenPullback (K : Type u) [Field K] :
    curveAffineEtaleCovers K ⥤ curveTwoPuncturedEtaleCovers K :=
  FiniteEtaleCover.pullback (curveTwoPuncturedOpenMap K)

/-- Pullback of finite etale covers of Spec K to the punctured curve. -/
abbrev curveTwoPuncturedStructurePullback (K : Type u) [Field K] :
    FiniteEtaleCover (Spec (CommRingCat.of K)) ⥤ curveTwoPuncturedEtaleCovers K :=
  FiniteEtaleCover.pullback (curveTwoPuncturedStructureMap K)

/-- Pullback of finite etale covers of Spec K to the affine curve. -/
abbrev curveAffineStructurePullback (K : Type u) [Field K] :
    FiniteEtaleCover (Spec (CommRingCat.of K)) ⥤ curveAffineEtaleCovers K :=
  FiniteEtaleCover.pullback (curveSchemeStructureMap K)

/-! ## 4. Actual covers from finite etale coordinate-ring algebras -/

/-- The structure morphism Spec A -> Spec R attached to a finite etale
R-algebra A. -/
def finiteEtaleAlgebraStructureMapOf (R : Type u) [CommRing R]
    (A : CommAlgCat.FiniteEtale R) :
    Spec (CommRingCat.of A.obj) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A.obj))

/-- The structure morphism of a finite etale R-algebra is etale. -/
theorem finiteEtaleAlgebraStructureMapOf_etale (R : Type u) [CommRing R]
    (A : CommAlgCat.FiniteEtale R) :
    Etale (finiteEtaleAlgebraStructureMapOf R A) := by
  rw [finiteEtaleAlgebraStructureMapOf]
  exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Etale) (Q := @RingHom.Etale)).mpr
    (RingHom.etale_algebraMap.mpr A.property.right)

/-- The structure morphism of a finite etale R-algebra is finite. -/
theorem finiteEtaleAlgebraStructureMapOf_finite (R : Type u) [CommRing R]
    (A : CommAlgCat.FiniteEtale R) :
    IsFinite (finiteEtaleAlgebraStructureMapOf R A) := by
  rw [finiteEtaleAlgebraStructureMapOf]
  exact (AlgebraicGeometry.IsFinite.SpecMap_iff
    (R := CommRingCat.of R) (S := CommRingCat.of A.obj)
    (f := CommRingCat.ofHom (algebraMap R A.obj))).mpr
    (RingHom.finite_algebraMap.mpr A.property.left)

/-- Every finite etale R-algebra gives an actual finite etale cover of Spec R. -/
def finiteEtaleAlgebraCoverOf (R : Type u) [CommRing R]
    (A : CommAlgCat.FiniteEtale R) :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  FiniteEtaleCover.mk (finiteEtaleAlgebraStructureMapOf R A)
    (finiteEtaleAlgebraStructureMapOf_etale R A)
    (finiteEtaleAlgebraStructureMapOf_finite R A)

/-- Object-level assignment from finite etale coordinate-ring algebras to
actual finite etale covers of the affine curve. -/
def curveCoordinateAlgebraCover (K : Type u) [Field K]
    (A : CommAlgCat.FiniteEtale (curveCoordinateRing K)) :
    curveAffineEtaleCovers K :=
  finiteEtaleAlgebraCoverOf (curveCoordinateRing K) A

/-- Every finite etale coordinate-ring algebra gives an actual finite etale
cover of the affine curve. -/
theorem curveCoordinateAlgebraCover_exists (K : Type u) [Field K]
    (A : CommAlgCat.FiniteEtale (curveCoordinateRing K)) :
    ∃ C : curveAffineEtaleCovers K,
      FiniteEtaleCover.carrier C = Spec (CommRingCat.of A.obj) :=
  ⟨curveCoordinateAlgebraCover K A, rfl⟩

/-! ## 5. Frozen card: Galois category, fiber functor, geometric connectedness
and curve pi-1 -/

/-- Frozen card: for a scheme S, the missing geometric connectedness, Galois
category structure, fiber functor and etale fundamental group data of its
finite etale cover category.  This is DATA: no inhabitant is constructed in
this file, the card is not proved and no theorem consumes it. -/
structure SchemeGaloisConnectednessCard (S : Scheme) where
  /-- The Galois category structure on finite etale covers. -/
  [galoisCategory : GaloisCategory (FiniteEtaleCover S)]
  /-- A fiber functor to finite sets. -/
  fiber : FiniteEtaleCover S ⥤ FintypeCat
  [fiberFunctor : PreGaloisCategory.FiberFunctor fiber]
  /-- The arithmetic etale fundamental group. -/
  fundamentalGroup : ProfiniteGrp
  /-- The action of the fundamental group on each fiber. -/
  action : ∀ X : FiniteEtaleCover S, MulAction fundamentalGroup (fiber.obj X)
  /-- The fundamental-group property. -/
  isFundamentalGroup :
    letI (X : FiniteEtaleCover S) := action X
    PreGaloisCategory.IsFundamentalGroup fiber fundamentalGroup
  /-- The geometric fundamental group. -/
  geometricPiOne : ProfiniteGrp
  /-- The exact geometric-connectedness statement for the base scheme S. -/
  geometricConnectedness : Prop

/-- The Galois/connectedness/pi-1 card for the affine curve. -/
abbrev curveAffineGaloisConnectednessCard (K : Type u) [Field K] :
    Type (u + 1) :=
  SchemeGaloisConnectednessCard (curveScheme K)

/-- The Galois/connectedness/pi-1 card for the punctured curve. -/
abbrev curveTwoPuncturedGaloisConnectednessCard (K : Type u) [Field K] :
    Type (u + 1) :=
  SchemeGaloisConnectednessCard (curveTwoPuncturedScheme K)

/-- The card is realized.  Frozen source obligation: not proved here and no
consumer. -/
def SchemeGaloisConnectednessCardRealized (S : Scheme) : Prop :=
  Nonempty (SchemeGaloisConnectednessCard S)

/-- The punctured-curve version of the frozen card realization proposition. -/
def curveTwoPuncturedGaloisConnectednessCardRealized (K : Type u) [Field K] : Prop :=
  SchemeGaloisConnectednessCardRealized (curveTwoPuncturedScheme K)

/-! ## Once-punctured source vs two-punctured extra category -/

/-- The ONCE-punctured source category: finite etale covers of the affine curve
curveScheme K = E \\ {O}.  This is the category used for the curve source; it is
definitionally the affine cover category curveAffineEtaleCovers K. -/
abbrev curveOncePuncturedEtaleCovers (K : Type u) [Field K] : Type (u + 1) :=
  curveAffineEtaleCovers K

/-- The terminal cover of the once-punctured source category. -/
abbrev curveOncePuncturedTerminalCover (K : Type u) [Field K] :
    curveOncePuncturedEtaleCovers K :=
  curveAffineTerminalCover K

/-- The card for the ONCE-punctured source E \\ {O} (the affine curve scheme). -/
abbrev curveOncePuncturedGaloisConnectednessCard (K : Type u) [Field K] :
    Type (u + 1) :=
  SchemeGaloisConnectednessCard (curveScheme K)

def curveOncePuncturedGaloisConnectednessCardRealized (K : Type u) [Field K] : Prop :=
  SchemeGaloisConnectednessCardRealized (curveScheme K)

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
