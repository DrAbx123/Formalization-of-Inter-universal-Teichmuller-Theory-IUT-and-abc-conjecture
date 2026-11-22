import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import Mathlib.Tactic

/-!
# Foundation F3a: the actual affine Weierstrass curve scheme y^2 = x^3 - x

Source anchor: IUT I/II, the D6 curve-Pi input; foundation item F3a.  This file
constructs an actual scheme model of the affine Weierstrass chart of the
projective closure of y^2 = x^3 - x over a field K, its structure morphism to
Spec K, and the two-punctured extra open subscheme obtained by removing the
finite point P = (0,0).  The affine model curveScheme K is already the
ONCE-punctured curve E \ {O} (the affine chart Z = 1 of the projective closure,
with O = (0:1:0) at infinity); removing P gives the TWO-punctured extra object
E \ {O,P}, which is not the once-punctured source.  The file also relates the
construction to the concrete rational Weierstrass curve
curveY2EqX3SubX of Example36EllipticCurveAnabelioid.lean.  The missing
projective closure and the missing etale-Pi-1/geometric-connectedness data are
frozen as precise cards, not asserted.

## Content

* curveEquationPolynomial K is the equation y^2 - x^3 + x in
  MvPolynomial (Fin 2) K (variable 0 is x, variable 1 is y);
  curveCoordinateRing K is the quotient K[x,y]/(y^2 - x^3 + x);
  curveScheme K = Spec (curveCoordinateRing K) is the actual affine scheme.
* curveSchemeStructureMap K : curveScheme K -> Spec K is the structure
  morphism induced by algebraMap K (curveCoordinateRing K); it is packaged as
  an object curveSchemeAsOver K of Over (Spec K).
* curveX, curveY are the images of the two coordinates in the quotient and
  curveWeierstrassRelation proves curveY^2 = curveX^3 - curveX in the
  coordinate ring (the actual equation, not a card).
* weierstrassAffinePolynomial is the general Weierstrass equation polynomial;
  weierstrassAffinePolynomial_curveY2EqX3SubX proves that for the concrete
  curveY2EqX3SubX over Q it equals the equation y^2 - x^3 + x used here.
* The origin (0,0) is realized by the kernel of the evaluation homomorphism
  curveOriginEval : curveCoordinateRing K -> K, proved maximal and surjective.
  curveOriginPoint is the corresponding closed point of curveScheme K, and
  curveTwoPuncturedOpens/curveTwoPuncturedScheme/curveTwoPuncturedOpenMap realize the
  complement of the finite point P = (0,0) as the TWO-punctured extra open
  subscheme E \ {O,P} with an open-immersion morphism to curveScheme K;
  curveTwoPuncturedAsOver K is its structure object over Spec K.  (The
  once-punctured source is curveScheme K itself, i.e. E \ {O}.)
* curveScheme_isAffine records that the model is affine.

## Frozen cards (not proved, no inhabitant, no consumer)

* CurveProjectiveClosureCard: the projective closure of y^2 = x^3 - x, its
  structure map over Spec K, the affine open comparison and the point at
  infinity.  Mathlib 4.32.2 has no Proj scheme API in this checkout, so this is
  a genuine gap.
* CurveEtaleFundamentalGroupCard: the finite etale cover category, Galois
  category structure, fiber functor and etale fundamental group of the
  punctured curve together with geometric connectedness data.  These are not
  constructed here; the card records the exact target interface.

No fake scheme, no fake Galois category and no card-only substitute for the
actual affine scheme construction are used.  No theta / q-pilot / Tate claim is
made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open AlgebraicGeometry CategoryTheory

universe u

/-! ## 1. The equation and the affine coordinate ring -/

/-- The affine Weierstrass equation y^2 - x^3 + x in K[x,y], with x = X 0 and
 y = X 1. -/
abbrev curveEquationPolynomial (K : Type u) [Field K] : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0

/-- The coordinate ideal (y^2 - x^3 + x) of K[x,y]. -/
abbrev curveCoordinateIdeal (K : Type u) [Field K] : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {curveEquationPolynomial K}

/-- The affine coordinate ring K[x,y]/(y^2 - x^3 + x) of the curve. -/
abbrev curveCoordinateRing (K : Type u) [Field K] : Type u :=
  MvPolynomial (Fin 2) K ⧸ curveCoordinateIdeal K

/-- The actual affine Weierstrass curve scheme Spec K[x,y]/(y^2 - x^3 + x). -/
abbrev curveScheme (K : Type u) [Field K] : Scheme :=
  Spec (CommRingCat.of (curveCoordinateRing K))

/-- The curve scheme is affine. -/
theorem curveScheme_isAffine (K : Type u) [Field K] : IsAffine (curveScheme K) :=
  inferInstance

/-! ## 2. Coordinates in the quotient and the curve equation -/

/-- The image of the x-coordinate in the coordinate ring. -/
abbrev curveX (K : Type u) [Field K] : curveCoordinateRing K :=
  Ideal.Quotient.mk (curveCoordinateIdeal K) (MvPolynomial.X 0)

/-- The image of the y-coordinate in the coordinate ring. -/
abbrev curveY (K : Type u) [Field K] : curveCoordinateRing K :=
  Ideal.Quotient.mk (curveCoordinateIdeal K) (MvPolynomial.X 1)

/-- The defining relation holds in the coordinate ring: y^2 = x^3 - x. -/
theorem curveWeierstrassRelation (K : Type u) [Field K] :
    curveY K ^ 2 = curveX K ^ 3 - curveX K := by
  have hmem : curveEquationPolynomial K ∈ curveCoordinateIdeal K :=
    Ideal.subset_span (Set.mem_singleton _)
  have hzero : (Ideal.Quotient.mk (curveCoordinateIdeal K)) (curveEquationPolynomial K) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have h : curveY K ^ 2 - curveX K ^ 3 + curveX K = 0 := by
    simpa [curveEquationPolynomial, curveX, curveY, map_add, map_sub, map_pow] using hzero
  linear_combination h

/-! ## 3. The structure morphism to Spec K -/

/-- The structure morphism curveScheme K -> Spec K induced by the algebra
structure map K -> K[x,y]/(y^2 - x^3 + x). -/
abbrev curveSchemeStructureMap (K : Type u) [Field K] :
    curveScheme K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (curveCoordinateRing K)))

/-- The curve scheme as an object of the category of schemes over Spec K. -/
abbrev curveSchemeAsOver (K : Type u) [Field K] :
    Over (Spec (CommRingCat.of K)) :=
  Over.mk (curveSchemeStructureMap K)

/-! ## 4. Relation to the concrete rational Weierstrass curve -/

/-- The general affine Weierstrass equation polynomial
Y^2 + a1 XY + a3 Y - (X^3 + a2 X^2 + a4 X + a6). -/
abbrev weierstrassAffinePolynomial {K : Type u} [Field K] (W : WeierstrassCurve K) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.X 1 ^ 2
    + MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.C W.a₃ * MvPolynomial.X 1
    - (MvPolynomial.X 0 ^ 3
      + MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2
      + MvPolynomial.C W.a₄ * MvPolynomial.X 0
      + MvPolynomial.C W.a₆)

/-- For the concrete curve y^2 = x^3 - x of Example36EllipticCurveAnabelioid,
the general Weierstrass polynomial is exactly the equation y^2 - x^3 + x used
here. -/
theorem weierstrassAffinePolynomial_curveY2EqX3SubX :
    weierstrassAffinePolynomial curveY2EqX3SubX = curveEquationPolynomial ℚ := by
  simp [weierstrassAffinePolynomial, curveEquationPolynomial, curveY2EqX3SubX]
  ring

/-! ## 5. The origin and the once-punctured open subscheme -/

/-- The evaluation at the origin (0,0) on polynomial rings. -/
abbrev curveOriginPolynomialEval (K : Type u) [Field K] :
    MvPolynomial (Fin 2) K →+* K :=
  MvPolynomial.eval (fun _ : Fin 2 => (0 : K))

/-- The evaluation at the origin factors through the coordinate ring. -/
abbrev curveOriginEval (K : Type u) [Field K] :
    curveCoordinateRing K →+* K :=
  Ideal.Quotient.lift (curveCoordinateIdeal K) (curveOriginPolynomialEval K) (by
    intro a ha
    have hle : curveCoordinateIdeal K ≤ RingHom.ker (curveOriginPolynomialEval K) := by
      rw [curveCoordinateIdeal, Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change curveOriginPolynomialEval K (curveEquationPolynomial K) = 0
      simp [curveOriginPolynomialEval, curveEquationPolynomial]
    exact hle ha)

/-- The evaluation at the origin is surjective. -/
theorem curveOriginEval_surjective (K : Type u) [Field K] :
    Function.Surjective (curveOriginEval K) := by
  intro y
  refine ⟨Ideal.Quotient.mk (curveCoordinateIdeal K) (MvPolynomial.C y), ?_⟩
  rw [curveOriginEval, Ideal.Quotient.lift_mk]
  simp [curveOriginPolynomialEval]

/-- The ideal of the origin (0,0) in the coordinate ring. -/
abbrev curveOriginIdeal (K : Type u) [Field K] : Ideal (curveCoordinateRing K) :=
  RingHom.ker (curveOriginEval K)

/-- The origin ideal is maximal (the evaluation is a surjection onto the
field K). -/
noncomputable instance curveOriginIdeal_isMaximal (K : Type u) [Field K] :
    (curveOriginIdeal K).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (curveOriginEval K) (curveOriginEval_surjective K)

/-- The origin (0,0) as a closed point of the curve scheme. -/
abbrev curveOriginPoint (K : Type u) [Field K] : curveScheme K :=
  ⟨curveOriginIdeal K, (curveOriginIdeal_isMaximal K).isPrime⟩

/-- The origin is a closed point. -/
theorem curveOriginPoint_isClosed (K : Type u) [Field K] :
    IsClosed ({curveOriginPoint K} : Set (curveScheme K)) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal (curveOriginPoint K)).mpr
    (curveOriginIdeal_isMaximal K)

/-- The open subscheme of the curve obtained by removing the origin. -/
def curveTwoPuncturedOpens (K : Type u) [Field K] : (curveScheme K).Opens :=
  ⟨({curveOriginPoint K} : Set (curveScheme K))ᶜ, (curveOriginPoint_isClosed K).isOpen_compl⟩

/-- The once-punctured curve as an actual open subscheme. -/
abbrev curveTwoPuncturedScheme (K : Type u) [Field K] : Scheme :=
  (curveTwoPuncturedOpens K : Scheme)

/-- The open immersion of the punctured curve into the affine curve. -/
abbrev curveTwoPuncturedOpenMap (K : Type u) [Field K] :
    curveTwoPuncturedScheme K ⟶ curveScheme K :=
  (curveTwoPuncturedOpens K).ι

/-- The open immersion of the punctured curve is an open immersion. -/
instance curveTwoPuncturedOpenMap_isOpenImmersion (K : Type u) [Field K] :
    IsOpenImmersion (curveTwoPuncturedOpenMap K) :=
  inferInstance

/-- The open range of the punctured-curve open immersion is exactly the
complement of the origin. -/
theorem curveTwoPuncturedOpenMap_opensRange (K : Type u) [Field K] :
    (curveTwoPuncturedOpenMap K).opensRange = curveTwoPuncturedOpens K :=
  Scheme.Opens.opensRange_ι _

/-- The structure morphism of the punctured curve over Spec K. -/
abbrev curveTwoPuncturedStructureMap (K : Type u) [Field K] :
    curveTwoPuncturedScheme K ⟶ Spec (CommRingCat.of K) :=
  curveTwoPuncturedOpenMap K ≫ curveSchemeStructureMap K

/-- The punctured curve as an object over Spec K. -/
abbrev curveTwoPuncturedAsOver (K : Type u) [Field K] :
    Over (Spec (CommRingCat.of K)) :=
  Over.mk (curveTwoPuncturedStructureMap K)

/-! ## Once-punctured vs two-punctured semantics (review F-R1 fix) -/

/-- The affine model curveScheme K = Spec K[x,y]/(y^2 - x^3 + x) is the affine
Weierstrass chart Z = 1 of the projective closure.  It is already the
ONCE-punctured curve E \\ {O}: the point at infinity O = (0:1:0) is the group
zero and is not part of the affine chart, while the finite point P = (0,0) is
present.  This is the source model for the curve. -/
abbrev curveOncePuncturedScheme (K : Type u) [Field K] : Scheme := curveScheme K

theorem curveOncePuncturedScheme_eq (K : Type u) [Field K] :
    curveOncePuncturedScheme K = curveScheme K := rfl

/-- The two-punctured scheme removes the finite point P = (0,0) from the
once-punctured affine model, hence is E \\ {O,P}; it is an EXTRA object and is
not the once-punctured source. -/
theorem curveTwoPuncturedScheme_eq (K : Type u) [Field K] :
    curveTwoPuncturedScheme K = (curveTwoPuncturedOpens K : Scheme) := rfl

/-- The finite point P = (0,0) is removed in the two-punctured scheme. -/
theorem curveOriginPoint_not_mem_twoPuncturedOpens (K : Type u) [Field K] :
    curveOriginPoint K ∉ curveTwoPuncturedOpens K := by
  simp [curveTwoPuncturedOpens]

/-! ## 6. Frozen cards -/
/-! ## 6. Frozen cards -/

/-- Frozen card: the projective closure of the affine curve y^2 = x^3 - x, its
structure map over Spec K, the affine open comparison and the point at
infinity.  Mathlib 4.32.2 in this checkout has no Proj scheme API, so this is
a genuine gap; the card is DATA with no inhabitant and no consumer. -/
structure CurveProjectiveClosureCard (K : Type u) [Field K] where
  /-- The projective Weierstrass curve scheme. -/
  projectiveScheme : Scheme
  /-- Its structure morphism over Spec K. -/
  projectiveStructureMap : projectiveScheme ⟶ Spec (CommRingCat.of K)
  /-- The affine open of the projective model. -/
  affineOpen : Scheme
  /-- The open immersion of the affine open. -/
  affineOpenMap : affineOpen ⟶ projectiveScheme
  [affineOpenMap_isOpenImmersion : IsOpenImmersion affineOpenMap]
  /-- The identification of the affine open with the coordinate-ring model. -/
  affineIso : affineOpen ≅ curveScheme K
  /-- The point at infinity. -/
  pointAtInfinity : projectiveScheme

/-- The projective closure card is realized.  Frozen source obligation: not
proved here and no consumer. -/
def CurveProjectiveClosureCardRealized (K : Type u) [Field K] : Prop :=
  Nonempty (CurveProjectiveClosureCard K)

/-- Frozen card: finite etale covers of the TWO-punctured extra curve E \ {O,P},
their Galois category, fiber functor, etale fundamental group and geometric
connectedness.  This card is for the extra two-punctured object, never for the
once-punctured source E \ {O} (which is curveScheme K).
None of this is constructed in this file; the card records the exact target
interface and has no inhabitant and no consumer. -/
structure CurveEtaleFundamentalGroupCard (K : Type u) [Field K] where
  /-- The category of finite etale covers of the punctured curve. -/
  coverCategory : Type u
  [coverCategory_category : Category coverCategory]
  [coverCategory_galoisCategory : GaloisCategory coverCategory]
  /-- The fiber functor. -/
  fiber : coverCategory ⥤ FintypeCat
  [fiber_fiberFunctor : PreGaloisCategory.FiberFunctor fiber]
  /-- The arithmetic etale fundamental group. -/
  fundamentalGroup : ProfiniteGrp
  /-- The action of the fundamental group on each fiber. -/
  action : ∀ X : coverCategory, MulAction fundamentalGroup (fiber.obj X)
  /-- The fundamental-group property, with the fiber actions as instances. -/
  isFundamentalGroup :
    letI (X : coverCategory) := action X
    PreGaloisCategory.IsFundamentalGroup fiber fundamentalGroup
  /-- The geometric fundamental group. -/
  geometricPiOne : ProfiniteGrp
  /-- Geometric connectedness of the curve (the precise predicate is the one
  used in the etale-Pi-1 theory of the punctured curve). -/
  geometricConnectedness : Prop

/-- The etale fundamental group card is realized.  Frozen source obligation:
not proved here and no consumer. -/
def CurveEtaleFundamentalGroupCardRealized (K : Type u) [Field K] : Prop :=
  Nonempty (CurveEtaleFundamentalGroupCard K)

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
