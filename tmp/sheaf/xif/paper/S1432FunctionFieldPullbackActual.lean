import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# S1432: the minimal TauCeti function-field / generic-point / field-pullback layer

Source: tmp/TauCeti (TauCeti, Lean v4.36.0-rc1). This file ports, to the current
checkout (Lean/Mathlib v4.32.2), the minimal layer that the isogeny count of TauCeti
uses:

* WeierstrassCurve.Affine.CoordinateRing evaluation lemmas
  (TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean,
  .../Affine/CoordinateRingMap.lean, .../Affine/Eval.lean);
* the generic point genericX, genericY, genericPoint
  (.../Affine/FunctionField/GenericPoint/Basic.lean);
* the coordinate accessors Point.xCoord, Point.yCoord and their compatibility with
  Mathlib's Point.map (.../Affine/Point/Basic.lean);
* the embedding statement map_genericPoint_injective: an F-algebra homomorphism out
  of the function field is determined by the point it sends the generic point to
  (.../Affine/FunctionField/GenericPoint/Basic.lean);
* the function-field pullback fieldPullback of a coordinate pullback, and its
  injectivity from nonconstancy (.../Isogeny/FunctionField.lean).

## What is ported

The coordinate ring is Mathlib's W.CoordinateRing (AdjoinRoot W.polynomial), and the
function field is Mathlib's W.FunctionField (FractionRing W.CoordinateRing). This file
adds the API TauCeti has on top of them.

## v4.32.2 adaptations

* Point.map already exists in Mathlib, but requires DecidableEq on both fields. The
  xCoord_map / yCoord_map and map_genericPoint_injective statements carry those
  hypotheses; a consumer can supply them from classical.
* TauCeti's Affine.instIsEllipticBaseChange is re-added, since Mathlib only registers
  (W.map f).IsElliptic, not the affine base-change spelling.
* Algebra.IsIntegral F[X] W.CoordinateRing is not an instance in Mathlib; it is
  installed here from Polynomial.Monic.finite_adjoinRoot.
* TauCeti's fieldPullback is IsFractionRing.liftAlgHom. Here it is built with
  AlgHom.mk around IsFractionRing.lift, with the same underlying ring hom: in
  v4.32.2 the liftAlgHom spelling makes the definitional unfolding of
  fieldPullback_algebraMap exceed the heartbeat budget, while the lift spelling keeps
  that lemma rfl-shaped and cheap.

## Exact first field

The ported layer is complete and compiles (EXIT=0). TauCeti.Isogeny.fieldPullback
needs pullback_injective, which needs CoordinateRing.algHom_injective and
transcendental_pullback_X; all three are below, as is fieldPullback_algebraMap.

The next field for the kernel count is
TauCeti.Isogeny.zsmul_map_sub_map_genericPoint_eq_zero, which needs the tautological
point of [n] and the multiplication-by-n isogeny (Isogeny/MulByInt/Basic.lean); that is
not part of this minimal layer.

## Provenance

TauCeti is Apache-2.0. The declarations ported here are attributed above by file.
-/

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] (W : Affine F)

instance coordinateRingModuleFinite : Module.Finite F[X] W.CoordinateRing :=
  Polynomial.Monic.finite_adjoinRoot W.monic_polynomial

instance coordinateRingIsIntegral : Algebra.IsIntegral F[X] W.CoordinateRing :=
  Algebra.IsIntegral.of_finite F[X] W.CoordinateRing

/-- **The class of a constant polynomial is its image under algebraMap.** -/
lemma mk_C_eq_algebraMap (r : F[X]) :
    CoordinateRing.mk W (C r) = algebraMap F[X] W.CoordinateRing r := by
  simp only [AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C]

/-- **Ring homomorphisms out of the coordinate ring are determined by the constants and the
classes of x and y.** -/
theorem ringHom_ext {T : Type*} [Semiring T] {f g : W.CoordinateRing →+* T}
    (hc : forall a : F, f (algebraMap F W.CoordinateRing a) = g (algebraMap F W.CoordinateRing a))
    (hx : f (AdjoinRoot.of W.polynomial X) = g (AdjoinRoot.of W.polynomial X))
    (hy : f (AdjoinRoot.root W.polynomial) = g (AdjoinRoot.root W.polynomial)) : f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      simpa only [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_eq]
        using hc a
    · exact hx
  · exact hy

/-- **An algebra homomorphism out of the coordinate ring is evaluation at the images of the two
coordinate functions**, the coefficients of the polynomial being carried into the target
algebra first. -/
theorem algHom_mk_eq_evalEval {A : Type*} [CommRing A] [Algebra F A]
    (f : W.CoordinateRing →ₐ[F] A) (p : F[X][Y]) :
    f (CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap F A))).evalEval
        (f (AdjoinRoot.of W.polynomial X)) (f (AdjoinRoot.root W.polynomial)) := by
  rw [← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X]
  let g : F[X][Y] →ₐ[F] A :=
    f.comp ((AdjoinRoot.mkₐ W.polynomial).restrictScalars F)
  change g p = _
  have hg : g = aevalAeval (g (C X)) (g Y) :=
    ((aevalAevalEquiv F A).apply_symm_apply g).symm
  rw [hg]
  let _ := Polynomial.algebra F A
  rw [aevalAevalEquiv_apply_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have halg : algebraMap F[X] A[X] = mapRingHom (algebraMap F A) := rfl
  rw [halg]
  simp only [g, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdjoinRoot.coe_mkₐ]

/-- **The images of the coordinate functions under an algebra homomorphism out of the coordinate
ring satisfy the Weierstrass equation** of the base-changed curve. -/
theorem equation_of_algHom {A : Type*} [CommRing A] [Algebra F A]
    (f : W.CoordinateRing →ₐ[F] A) :
    (W⁄A).Equation (f (AdjoinRoot.of W.polynomial X)) (f (AdjoinRoot.root W.polynomial)) := by
  change (W.map (algebraMap F A)).Equation _ _
  rw [Equation, map_polynomial,
    ← algHom_mk_eq_evalEval W f W.polynomial, AdjoinRoot.mk_self, map_zero]

/-- **An algebra homomorphism out of the coordinate ring under which the coordinate x stays
transcendental is injective.** A nonzero element of the kernel has nonzero norm over F[x], and
that norm is a polynomial relation killing the image of x. -/
theorem algHom_injective {A : Type*} [CommRing A] [Algebra F A]
    (f : W.CoordinateRing →ₐ[F] A)
    (hx : Transcendental F (f (CoordinateRing.mk W (C X)))) : Function.Injective f := by
  apply (injective_iff_map_eq_zero f).2
  intro z hz
  by_contra hz0
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq z
  set N : F[X] := Algebra.norm F[X] z with hN_def
  have hN0 : N ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis W)).2 hz0
  have hnorm : algebraMap F[X] W.CoordinateRing N =
      z * CoordinateRing.mk W
        (C p + C q * (-(Y : F[X][Y]) - C (C W.a₁ * X + C W.a₃))) := by
    rw [hN_def, ← hpq]
    simpa [CoordinateRing.smul] using
      CoordinateRing.coe_norm_smul_basis (W' := W) p q
  refine hx ⟨N, hN0, ?_⟩
  have hhom : Polynomial.aeval
      (f (CoordinateRing.mk W (C X))) =
      f.comp (IsScalarTower.toAlgHom F F[X] W.CoordinateRing) := by
    apply Polynomial.algHom_ext
    simp
  rw [AlgHom.congr_fun hhom N, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, hnorm, map_mul,
    hz, zero_mul]

/-- The structure map F[X] to F[W] is injective: a nonzero constant polynomial is not a
multiple of the monic quadratic W.polynomial. -/
theorem of_injective : Function.Injective (AdjoinRoot.of W.polynomial) := by
  intro a b h
  have h1 : AdjoinRoot.mk W.polynomial (C a) = AdjoinRoot.mk W.polynomial (C b) := by
    simpa only [AdjoinRoot.mk_C] using h
  rw [AdjoinRoot.mk_eq_mk] at h1
  by_contra hab
  have hne : (C (a - b) : F[X][Y]) ≠ 0 := by
    rw [Polynomial.C_ne_zero, sub_ne_zero]
    exact hab
  have hdvd : W.polynomial ∣ (C (a - b) : F[X][Y]) := by
    rw [Polynomial.C_sub]
    exact h1
  have hdeg : W.polynomial.natDegree ≤ (C (a - b) : F[X][Y]).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hne
  rw [natDegree_polynomial, Polynomial.natDegree_C] at hdeg
  omega

/-- The structure map F[X] to F(W) is injective. -/
theorem algebraMap_FX_injective : Function.Injective (algebraMap F[X] W.FunctionField) := by
  rw [IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField]
  refine (IsFractionRing.injective W.CoordinateRing W.FunctionField).comp ?_
  intro a b h
  exact of_injective W (by simpa [AdjoinRoot.algebraMap_eq] using h)

end CoordinateRing

/-- Mathlib carries ellipticity through WeierstrassCurve.map; this exposes the same instance for
the affine base-change spelling W/A. -/
instance instIsEllipticBaseChange {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (W : Affine R) [W.IsElliptic] : (W⁄A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

section GenericPoint

variable {F : Type*} [Field F] (W : Affine F)

/-- The generic x-coordinate: the class of X in the function field. -/
def genericX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))

/-- The generic y-coordinate: the class of Y in the function field. -/
def genericY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

/-- The generic coordinate x is the image of the coordinate-ring class of X in the function
field. -/
theorem genericX_def :
    genericX W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)) := (rfl)

/-- The generic coordinate y is the image of the coordinate-ring class of Y in the function
field. -/
theorem genericY_def :
    genericY W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) := (rfl)

/-- The generic coordinate x is the image of the polynomial X under the induced map from F[X]
to the function field. -/
theorem genericX_eq_algebraMap : genericX W = algebraMap F[X] W.FunctionField X := by
  rw [genericX_def, CoordinateRing.mk_C_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField X).symm

variable {W} in
/-- **Ring homomorphisms out of the function field are determined by the constants and the generic
coordinates.** -/
theorem FunctionField.ringHom_ext {S : Type*} [Semiring S] {f g : W.FunctionField →+* S}
    (hc : forall a : F, f (algebraMap F W.FunctionField a) = g (algebraMap F W.FunctionField a))
    (hx : f W.genericX = g W.genericX) (hy : f W.genericY = g W.genericY) : f = g := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors W.CoordinateRing) <|
    CoordinateRing.ringHom_ext W (fun a => ?_) ?_ ?_
  · simpa only [IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField,
      RingHom.comp_apply] using hc a
  · simpa [genericX_def, CoordinateRing.mk_C_eq_algebraMap] using hx
  · simpa [genericY_def] using hy

/-- **Evaluating at the generic point is reduction modulo the Weierstrass relation.** -/
theorem evalEval_genericX_genericY (p : F[X][Y]) :
    (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval W.genericX W.genericY =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p) :=
  (CoordinateRing.algHom_mk_eq_evalEval W
    (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField) p).symm

/-- **The generic coordinate functions satisfy the equation of the curve.** -/
theorem equation_genericX_genericY :
    (W⁄W.FunctionField).Equation W.genericX W.genericY :=
  CoordinateRing.equation_of_algHom W
    (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField)

section IsElliptic

variable [W.IsElliptic]

/-- The generic coordinates are nonsingular, so they define an affine point of the base-changed
curve. -/
theorem nonsingular_genericX_genericY :
    (W⁄W.FunctionField).Nonsingular W.genericX W.genericY :=
  equation_iff_nonsingular.mp (equation_genericX_genericY W)

/-- **The generic point of W**: the tautological point of W with coordinates in its own
function field. -/
def genericPoint : (W⁄W.FunctionField).Point :=
  .some _ _ (nonsingular_genericX_genericY W)

/-- The generic point is the affine point whose coordinates are genericX W and genericY W. -/
theorem genericPoint_eq_some : genericPoint W =
    .some (genericX W) (genericY W) (nonsingular_genericX_genericY W) := (rfl)

end IsElliptic

/-- **The coordinate function x is transcendental over the base field.** -/
theorem transcendental_genericX : Transcendental F (genericX W) := by
  rw [genericX_eq_algebraMap]
  exact (transcendental_algebraMap_iff (CoordinateRing.algebraMap_FX_injective W)).2
    (Polynomial.transcendental_X F)

end GenericPoint

namespace Point

variable {R : Type*} [CommRing R] {W : Affine R}

/-- The x-coordinate of a point, taken to be 0 at the point at infinity. -/
def xCoord : W.Point → R
  | 0 => 0
  | .some x _ _ => x

/-- The y-coordinate of a point, taken to be 0 at the point at infinity. -/
def yCoord : W.Point → R
  | 0 => 0
  | .some _ y _ => y

@[simp]
theorem xCoord_zero : xCoord (0 : W.Point) = 0 := (rfl)

@[simp]
theorem yCoord_zero : yCoord (0 : W.Point) = 0 := (rfl)

@[simp]
theorem xCoord_some {x y : R} (h : W.Nonsingular x y) : xCoord (.some x y h) = x := (rfl)

@[simp]
theorem yCoord_some {x y : R} (h : W.Nonsingular x y) : yCoord (.some x y h) = y := (rfl)

variable {S F1 K : Type*} [CommRing S] [Field F1] [Field K] [Algebra R S] [Algebra R F1]
  [Algebra S F1] [IsScalarTower R S F1] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  [DecidableEq F1] [DecidableEq K]

/-- **The x-coordinate commutes with Point.map.** -/
theorem xCoord_map (f : F1 →ₐ[S] K) (P : (W⁄F1).Point) :
    xCoord (Point.map f P) = f (xCoord P) := by
  cases P with
  | zero => exact f.toRingHom.map_zero.symm
  | some x y h => (rfl)

/-- **The y-coordinate commutes with Point.map.** -/
theorem yCoord_map (f : F1 →ₐ[S] K) (P : (W⁄F1).Point) :
    yCoord (Point.map f P) = f (yCoord P) := by
  cases P with
  | zero => exact f.toRingHom.map_zero.symm
  | some x y h => (rfl)

end Point

section GenericPointEmbedding

variable {F : Type*} [Field F] (W : Affine F) [W.IsElliptic]

@[simp]
theorem xCoord_genericPoint :
    Point.xCoord (genericPoint W) = genericX W :=
  Point.xCoord_some _

@[simp]
theorem yCoord_genericPoint :
    Point.yCoord (genericPoint W) = genericY W :=
  Point.yCoord_some _

/-- **An F-embedding of the function field into a field extension is determined by the image of
the generic point.** -/
theorem map_genericPoint_injective {Om : Type*} [Field Om] [Algebra F Om]
    [DecidableEq F] [DecidableEq W.FunctionField] [DecidableEq Om] :
    Function.Injective fun sigma : W.FunctionField →ₐ[F] Om =>
      Point.map (W' := W) sigma (genericPoint W) := by
  intro sigma tau h
  have hx : sigma (genericX W) = tau (genericX W) := by
    simpa only [Point.xCoord_map, xCoord_genericPoint] using congrArg Point.xCoord h
  have hy : sigma (genericY W) = tau (genericY W) := by
    simpa only [Point.yCoord_map, yCoord_genericPoint] using congrArg Point.yCoord h
  apply AlgHom.coe_ringHom_injective
  exact FunctionField.ringHom_ext (W := W) (fun a => by simp) hx hy

end GenericPointEmbedding

end WeierstrassCurve.Affine


/-! ## The isogeny function-field pullback -/

namespace TauCeti

open WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-- A contravariant pullback from the target coordinate ring to the source function field. -/
abbrev CoordinatePullback (W1 W2 : Affine F) : Type _ :=
  W2.CoordinateRing →ₐ[F] W1.FunctionField

namespace CoordinatePullback

/-- The source point at infinity maps to the target point at infinity: every element of the
source coordinate ring is integral over the target coordinate ring acting through pullback. -/
def MapsInfinity {W1 W2 : Affine F} (pullback : CoordinatePullback W1 W2) : Prop :=
  letI := pullback.toRingHom.toAlgebra
  forall x : W1.CoordinateRing,
    algebraMap W1.CoordinateRing W1.FunctionField x ∈
      integralClosure W2.CoordinateRing W1.FunctionField

/-- A coordinate pullback maps infinity to infinity exactly when the source coordinate ring is
integral over the target coordinate ring acting through the pullback. -/
@[simp]
theorem mapsInfinity_iff {W1 W2 : Affine F} (pullback : CoordinatePullback W1 W2) :
    pullback.MapsInfinity ↔ forall x : W1.CoordinateRing,
      @IsIntegral W2.CoordinateRing W1.FunctionField _ _ pullback.toRingHom.toAlgebra
        (algebraMap W1.CoordinateRing W1.FunctionField x) :=
  Iff.rfl

end CoordinatePullback

/-- The pullback data of a nonzero isogeny between affine Weierstrass curves. -/
@[ext]
structure Isogeny (W1 W2 : Affine F) where
  /-- The contravariant map out of the target coordinate ring. -/
  pullback : CoordinatePullback W1 W2
  /-- The source point at infinity maps to the target point at infinity. -/
  mapsInfinity : pullback.MapsInfinity

namespace Isogeny

variable {W1 W2 W3 : Affine F}

private theorem isIntegral_eval_of_isIntegral {K : Type*} [CommRing K] [Algebra F K]
    {x : K} (hx : IsIntegral F x) (p : F[X]) : IsIntegral F (aeval x p) := by
  rw [← mem_integralClosure_iff]
  exact adjoin_le_integralClosure hx (Polynomial.aeval_mem_adjoin_singleton F x)

-- Integrality descends along a ring hom with integral image.
private theorem isIntegral_of_isIntegral_map {R A K : Type*} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R K] (f : A →+* K) (hf : forall a, IsIntegral R (f a)) {x : K}
    (hx : @IsIntegral A K _ _ f.toAlgebra x) : IsIntegral R x :=
  let _ := f.toAlgebra
  isIntegral_trans x (hx.map_of_comp_eq (f.codRestrict (integralClosure R K) hf) (RingHom.id K) rfl)

private theorem isIntegral_pullback_of_isIntegral_X (phi : Isogeny W1 W2)
    (hX : IsIntegral F (phi.pullback (algebraMap F[X] W2.CoordinateRing X)))
    (a : W2.CoordinateRing) : IsIntegral F (phi.pullback a) := by
  obtain ⟨P, hPmonic, hPa⟩ :=
    (Algebra.IsIntegral.isIntegral (R := F[X]) a : IsIntegral F[X] a)
  let e : F[X] →ₐ[F] W1.FunctionField :=
    phi.pullback.comp (IsScalarTower.toAlgHom F F[X] W2.CoordinateRing)
  have he_ring : e.toRingHom =
      phi.pullback.toRingHom.comp (algebraMap F[X] W2.CoordinateRing) := by
    ext r
    · exact congr_arg phi.pullback
        (IsScalarTower.toAlgHom_apply F F[X] W2.CoordinateRing (C r))
    · exact congr_arg phi.pullback
        (IsScalarTower.toAlgHom_apply F F[X] W2.CoordinateRing X)
  have he : e = aeval (phi.pullback (algebraMap F[X] W2.CoordinateRing X)) := by
    apply Polynomial.algHom_ext
    simp [e]
  apply isIntegral_of_isIntegral_map e.toRingHom (x := phi.pullback a)
  · intro p
    rw [he]
    exact isIntegral_eval_of_isIntegral hX p
  · refine ⟨P, hPmonic, ?_⟩
    rw [e.toRingHom.algebraMap_toAlgebra, he_ring]
    exact
      (Polynomial.hom_eval₂ P (algebraMap F[X] W2.CoordinateRing)
        phi.pullback.toRingHom a).symm.trans (by rw [hPa, map_zero])

/-- **The pullback of the affine coordinate is transcendental.** -/
theorem transcendental_pullback_X (phi : Isogeny W1 W2) :
    Transcendental F (phi.pullback (algebraMap F[X] W2.CoordinateRing X)) := by
  intro ht_algebraic
  have himage : forall a : W2.CoordinateRing, IsIntegral F (phi.pullback a) :=
    isIntegral_pullback_of_isIntegral_X phi ht_algebraic.isIntegral
  let x1 : W1.FunctionField :=
    algebraMap W1.CoordinateRing W1.FunctionField
      (algebraMap F[X] W1.CoordinateRing X)
  have hx1_over_target :
      @IsIntegral W2.CoordinateRing W1.FunctionField _ _
        phi.pullback.toRingHom.toAlgebra x1 :=
    (CoordinatePullback.mapsInfinity_iff phi.pullback).1 phi.mapsInfinity
      (algebraMap F[X] W1.CoordinateRing X)
  have hx1 : IsIntegral F x1 :=
    isIntegral_of_isIntegral_map phi.pullback.toRingHom himage hx1_over_target
  have hx1_transcendental : Transcendental F x1 := by
    have hx1_eq : x1 = genericX W1 := by
      rw [genericX_def, CoordinateRing.mk_C_eq_algebraMap]
    rw [hx1_eq]
    exact transcendental_genericX W1
  exact hx1_transcendental hx1.isAlgebraic

/-- **The coordinate pullback of any isogeny is injective**, by the general criterion
CoordinateRing.algHom_injective. -/
theorem pullback_injective (phi : Isogeny W1 W2) : Function.Injective phi.pullback :=
  CoordinateRing.algHom_injective W2 phi.pullback <| by
    rw [CoordinateRing.mk_C_eq_algebraMap]
    exact phi.transcendental_pullback_X

/-- The function-field pullback induced by an isogeny: the unique extension of the coordinate
pullback across the target fraction field. -/
noncomputable def fieldPullback (phi : Isogeny W1 W2) :
    W2.FunctionField →ₐ[F] W1.FunctionField :=
  AlgHom.mk
    (IsFractionRing.lift (g := (phi.pullback : W2.CoordinateRing →+* W1.FunctionField))
      (show Function.Injective (phi.pullback : W2.CoordinateRing →+* W1.FunctionField) from
        phi.pullback_injective))
    (fun r => by
      rw [IsScalarTower.algebraMap_apply F W2.CoordinateRing W2.FunctionField]
      exact (IsFractionRing.lift_algebraMap
        (g := (phi.pullback : W2.CoordinateRing →+* W1.FunctionField))
        (show Function.Injective (phi.pullback : W2.CoordinateRing →+* W1.FunctionField) from
          phi.pullback_injective)
        (algebraMap F W2.CoordinateRing r)).trans (phi.pullback.commutes r))

/-- The function-field pullback restricts to the original coordinate pullback. -/
@[simp]
theorem fieldPullback_algebraMap (phi : Isogeny W1 W2) (x : W2.CoordinateRing) :
    phi.fieldPullback (algebraMap W2.CoordinateRing W2.FunctionField x) = phi.pullback x :=
  IsFractionRing.lift_algebraMap
    (g := (phi.pullback : W2.CoordinateRing →+* W1.FunctionField))
    (show Function.Injective (phi.pullback : W2.CoordinateRing →+* W1.FunctionField) from
      phi.pullback_injective) x

end Isogeny

end TauCeti