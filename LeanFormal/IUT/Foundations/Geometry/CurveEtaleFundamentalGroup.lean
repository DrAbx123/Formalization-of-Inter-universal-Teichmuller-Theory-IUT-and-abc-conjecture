/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import Mathlib

set_option linter.unusedSectionVars false

/-!
# The once-punctured elliptic curve as a scheme and its finite etale covers

Task task-133.  This module constructs the actual geometric foundation for the
source curve Pi_v:

* the affine scheme of the once-punctured elliptic curve y^2 = x^3 - x over a
  field K as Spec of the coordinate ring K[X,Y]/(Y^2 - X^3 + X), with its
  structure morphism to Spec K;
* the category of finite etale covers of a scheme X: the full subcategory of
  schemes over X on etale, finite structure morphisms (Mathlib's Etale and
  IsFinite morphism properties);
* the geometric fiber functor at a geometric point x : Spec Omega -> X: a
  finite etale cover Y -> X is sent to the type of lifts of x to Y, and
  morphisms act by postcomposition; functoriality is proved;
* the actual geometric etale fundamental group as the automorphism group of the
  fiber functor (Mathlib's Aut, with its Group instance);
* the interface CurvePiOneData with the profinite group, projection to the
  Galois group, geometric kernel and comparison function which a future full
  etale Pi_v computation must provide.

## Exact missing API (no card, no fake Pi_1)

Mathlib 4.32.2 has the morphism properties Etale and IsFinite and the category
Over X, but it has NO theorem that finite etale covers of a scheme form a Galois
category with a fundamental-group certificate (PreGaloisCategory.
IsFundamentalGroup is available only for the field-side Galois categories), NO
profinite topology on the fiber-functor automorphism group of a scheme, NO
canonical surjection pi_1^et(X) -> Gal(Kbar/K) with geometric kernel, and NO
geometric action on the local value monoid.  The group constructed below is
therefore the actual automorphism group of the actual geometric fiber functor,
not yet a profinite group; CurvePiOneData is an interface whose fields are data
to be supplied by future geometric work.  No unproved placeholder, no card and
no fake curve is introduced.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.Foundations.Geometry

universe u

/-! ## 1. The affine once-punctured elliptic curve y^2 = x^3 - x -/

/-- The defining equation y^2 - x^3 + x of the elliptic curve y^2 = x^3 - x in
affine coordinates x = X 0, y = X 1. -/
def puncturedEllipticEquation (K : Type u) [Field K] : MvPolynomial (Fin 2) K :=
  (MvPolynomial.X 1) ^ 2 - (MvPolynomial.X 0) ^ 3 + MvPolynomial.X 0

/-- The coordinate ring K[X,Y]/(Y^2 - X^3 + X) of the affine once-punctured
curve y^2 = x^3 - x (the puncture is the point at infinity). -/
abbrev puncturedEllipticCoordinateRing (K : Type u) [Field K] : Type u :=
  MvPolynomial (Fin 2) K ⧸
    Ideal.span ({puncturedEllipticEquation K} : Set (MvPolynomial (Fin 2) K))

/-- The affine scheme of the once-punctured elliptic curve. -/
abbrev puncturedEllipticCurveScheme (K : Type u) [Field K] : Scheme.{u} :=
  Spec (CommRingCat.of (puncturedEllipticCoordinateRing K))

/-- The structure morphism to the base field, from the constants K inside the
coordinate ring. -/
def puncturedEllipticCurveStructureMorphism (K : Type u) [Field K] :
    puncturedEllipticCurveScheme K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span
      ({puncturedEllipticEquation K} : Set (MvPolynomial (Fin 2) K)))).comp
      (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K)))

/-! ## 2. Finite etale covers -/

/-- The object property of a finite etale cover of a scheme X. -/
def finiteEtaleCoverProperty (X : Scheme.{u}) : ObjectProperty (Over X) :=
  fun Y => Etale Y.hom ∧ IsFinite Y.hom

/-- The category of finite etale covers of X. -/
abbrev FiniteEtaleCover (X : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (finiteEtaleCoverProperty X)

instance (X : Scheme.{u}) : Category.{u, u + 1} (FiniteEtaleCover X) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory
    (finiteEtaleCoverProperty X)))

/-- Forgetful functor from finite etale covers of X to schemes over X. -/
def finiteEtaleCoverForget (X : Scheme.{u}) :
    FiniteEtaleCover X ⥤ Over X :=
  ObjectProperty.ι (finiteEtaleCoverProperty X)

/-- The underlying scheme of a finite etale cover. -/
abbrev finiteEtaleCoverScheme {X : Scheme.{u}} (Y : FiniteEtaleCover X) : Scheme.{u} :=
  Y.1.left

/-- The structure morphism of a finite etale cover. -/
abbrev finiteEtaleCoverStructure {X : Scheme.{u}} (Y : FiniteEtaleCover X) :
    finiteEtaleCoverScheme Y ⟶ X :=
  Y.1.hom

/-! ## 3. The geometric fiber functor -/

/-- The geometric fiber of a finite etale cover Y -> X at a geometric point x:
the type of lifts of x to Y. -/
def geometricFiberObject {X : Scheme.{u}} (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ X) (Y : FiniteEtaleCover X) : Type u :=
  { s : Spec (CommRingCat.of Omega) ⟶ finiteEtaleCoverScheme Y //
    s ≫ finiteEtaleCoverStructure Y = x }

/-- Action of a morphism of finite etale covers on geometric fibers, by
postcomposition. -/
def geometricFiberMap {X : Scheme.{u}} {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ X} {Y Z : FiniteEtaleCover X}
    (f : Y ⟶ Z) (s : geometricFiberObject Omega x Y) :
    geometricFiberObject Omega x Z :=
  ⟨s.1 ≫ (Over.Hom.left f.1), by
    rw [Category.assoc, Over.w f.1, s.2]⟩

/-- The geometric fiber functor at a geometric point of X. -/
def geometricFiberFunctor {X : Scheme.{u}} (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ X) :
    FiniteEtaleCover X ⥤ Type u where
  obj := geometricFiberObject Omega x
  map f := TypeCat.ofHom (fun s => geometricFiberMap (Omega := Omega) (x := x) f s)
  map_id Y := by rfl
  map_comp f g := by rfl

/-- The actual geometric etale fundamental group: the automorphism group of the
geometric fiber functor.  It is a group, but not yet a profinite group (the
Galois-category certificate for finite etale covers of a scheme is missing in
Mathlib 4.32.2). -/
abbrev curveEtaleFundamentalGroup {X : Scheme.{u}} (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ X) :=
  Aut (geometricFiberFunctor Omega x)

instance {X : Scheme.{u}} {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ X) :
    Group (curveEtaleFundamentalGroup Omega x) :=
  inferInstance

/-! ## 4. The geometric Pi_v interface -/

/-- Interface data for a full etale Pi_v computation of the curve: a profinite
group Pi with a profinite Galois group G, a surjective projection, the
geometric kernel, and a comparison function from the actual fiber-functor
automorphism group.  Every field is data to be supplied; no existence is
asserted and no card is introduced. -/
structure CurvePiOneData {X : Scheme.{u}} (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ X) where
  /-- the profinite etale fundamental group Pi_v -/
  Pi : ProfiniteGrp.{u}
  /-- the profinite local Galois group G_v -/
  G : ProfiniteGrp.{u}
  /-- the projection Pi_v -> G_v -/
  piToGalois : Pi ⟶ G
  /-- the projection is surjective -/
  piToGalois_surjective : Function.Surjective piToGalois
  /-- comparison of the fiber-functor automorphism group with Pi_v -/
  comparison : curveEtaleFundamentalGroup Omega x → (Pi : Type u)
  /-- the geometric kernel of Pi_v -/
  geometricKernel : Subgroup (Pi : Type u)
  /-- the geometric kernel is the kernel of the projection -/
  geometricKernel_eq : geometricKernel = piToGalois.hom.toMonoidHom.ker

/-- If the geometric kernel of the Pi_v data is trivial, the projection is
injective; nontriviality of the kernel is exactly the nontrivial geometric
fundamental group phenomenon. -/
theorem CurvePiOneData.geometricKernel_eq_bot_iff {X : Scheme.{u}} {Omega : Type u}
    [Field Omega] {x : Spec (CommRingCat.of Omega) ⟶ X} (D : CurvePiOneData Omega x) :
    D.geometricKernel = ⊥ ↔ Function.Injective D.piToGalois := by
  rw [D.geometricKernel_eq]
  exact MonoidHom.ker_eq_bot_iff D.piToGalois.hom.toMonoidHom

end LeanFormal.IUT.Foundations.Geometry
