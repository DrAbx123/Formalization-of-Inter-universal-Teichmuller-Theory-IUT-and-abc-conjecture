/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.Algebra.Module.Torsion.Basic
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual

/-!
# S1430: the minimal layer of TauCeti's `Isogeny/MulByInt/Basic.lean` at Lean v4.32.2

This file ports the definitional and generic-point part of
`TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Basic.lean` (Lean
v4.36.0-rc1) to the Mathlib v4.32.2 checkout in this workspace, together with
the small pieces of `Affine/Eval.lean`, `Affine/FunctionField/GenericPoint/Basic.lean`
and `Isogeny/Basic.lean` that it consumes.  The bivariate `ω` and `ψc` are
taken from the already-ported `S1410BivariateOmegaActual`; they are not
vendored again.

## What is ported, with proofs

* the coordinate-ring evaluation homomorphism `CoordinateRing.evalAlgHom`,
  its computation rules, and `CoordinateRing.equation_of_algHom`;
* the generic point `genericX`, `genericY`, `genericPoint` and the equation
  `equation_genericX_genericY`;
* `psiFunctionField`, `omegaFunctionField`, `phiFunctionField`,
  `psicFunctionField`, `mulByIntX`, `mulByIntY` and their defining
  equations;
* `phiFunctionField_eq_algebraMap`, `psiFunctionField_sq`,
  `psiFunctionField_two_mul`, `aeval_genericX_Φ`, `aeval_genericX_ΨSq`,
  `mulByIntX_mul_aeval_ΨSq`, `ΨSq_eq_zero_of_psiFunctionField_eq_zero`,
  and the `(n : F) ≠ 0` nonvanishing `psiFunctionField_ne_zero`;
* `CoordinatePullback`, `CoordinatePullback.MapsInfinity`, `Isogeny`, the
  tautological point of a coordinate pullback, and the conditional
  `mulByIntPullback` / `mulByIntIsogeny`;
* the concrete `n = 1` instance: the equation, the pullback, and the
  identity isogeny, so the conditional layer is not vacuous.

## The exact first field

The source's `equation_mulByInt` is

  `(W⁄W.FunctionField).Equation (mulByIntX W n) (mulByIntY W n)`

for `psiFunctionField W n ≠ 0`.  Here it is the named proposition
`EquationMulByInt W n`, and it is *not assumed*: every construction that needs
it takes it as an explicit argument.  In TauCeti its proof is
`WeierstrassCurve.zsmul_point_eq_smulEval`, the division-polynomial formula
for `n • P`; the proof needs `IsEllipticNet (normEDS b c d)`, an explicit
TODO in Mathlib v4.32.2 (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`),
together with the bivariate `ω` point-evaluation bridge.  That is the exact
first field of this port.

The second field is `MapsInfinityMulByInt`: `MapsInfinity` of the pullback,
which TauCeti proves from the equation via `mapsInfinity_iff_isIntegralElem_genericX`
and `monic_Φ_sub_C_mul_ΨSq`; neither lemma is available at this Mathlib pin.

The tautological-point identification `TautologicalPointMulByInt`
(`tautologicalPoint of [n] = n • genericPoint`) is likewise a named
proposition, not assumed.  The source's kernel identification
`ker [n] = W.Point[n]` is not stated as a proposition, because the minimal
`TauCeti.Isogeny` here has no `ker` field: the source defines `ker` through
the translation action on the function field, whose fixed-field development is
outside this minimal layer.  The concrete kernel object `mulByIntKer` is
Mathlib's `AddSubgroup.torsionBy W.Point n`, the right-hand side of TauCeti's
`ker_mulByIntIsogeny_eq_torsionBy`.

## Provenance

The declarations are adapted from TauCeti
`AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Basic.lean`,
`Affine/Eval.lean`, `Affine/FunctionField/GenericPoint/Basic.lean` and
`Isogeny/Basic.lean` (Apache-2.0).  The nonsingularity-free statement
`equation_genericX_genericY` is the port of AINTLIB's `generic_equation`.
No TauCeti universal-curve, ZSMul or translation closure is vendored.

## Status

`statement_compiles`: checked by `lake env lean` (see the reported EXIT).
`proof_body_checked`: yes for every declaration in this file except the three
named input propositions (`EquationMulByInt`, `MapsInfinityMulByInt`,
`TautologicalPointMulByInt`), which are `Prop`-valued definitions with no
inhabitants asserted.  The `n = 1` equation, pullback, `MapsInfinity` proof
and isogeny are all fully proved.
`kernel_closed`: no; the exact first field is `EquationMulByInt`.
`target_accepted`: no; D5 remains open at `EquationMulByInt`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

/-! ## 1. The coordinate ring and its evaluation homomorphism -/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace CoordinateRing

/-- The class of a univariate polynomial is its image under the algebra map. -/
theorem mk_C_eq_algebraMap (p : F[X]) :
    CoordinateRing.mk W (C p) = algebraMap F[X] W.CoordinateRing p := by
  rw [CoordinateRing.mk, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

/-- The base change `F[X] → F[W]` is injective. -/
theorem algebraMap_FX_injective :
    Function.Injective (algebraMap F[X] W.CoordinateRing) := by
  rw [AdjoinRoot.algebraMap_eq]
  refine AdjoinRoot.of.injective_of_degree_ne_zero ?_
  rw [Polynomial.degree_eq_natDegree W.monic_polynomial.ne_zero, W.natDegree_polynomial]
  norm_num

/-- The composite `F[X] → F[W] → F(W)` is injective. -/
theorem algebraMap_FX_functionField_injective :
    Function.Injective (algebraMap F[X] W.FunctionField) := by
  rw [IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField]
  exact (IsFractionRing.injective W.CoordinateRing W.FunctionField).comp
    (algebraMap_FX_injective W)

/-- Two algebra homomorphisms out of the coordinate ring agreeing on the two
coordinate functions are equal. -/
@[ext]
theorem algHom_ext {W : WeierstrassCurve.Affine F} {A : Type*} [Semiring A] [Algebra F A]
    {f g : W.CoordinateRing →ₐ[F] A}
    (hX : f (AdjoinRoot.of W.polynomial X) = g (AdjoinRoot.of W.polynomial X))
    (hY : f (AdjoinRoot.root W.polynomial) = g (AdjoinRoot.root W.polynomial)) :
    f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    simpa using hX
  · exact hY

/-- An algebra homomorphism out of the coordinate ring is evaluation at the
images of the two coordinate functions. -/
theorem algHom_mk_eq_evalEval {W : WeierstrassCurve.Affine F} {A : Type*} [CommSemiring A] [Algebra F A]
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
  rw [aevalAevalEquiv_apply_apply, Polynomial.aeval_def, eval₂_eq_eval_map]
  have halg : algebraMap F[X] A[X] = mapRingHom (algebraMap F A) := rfl
  rw [halg]
  simp only [g, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdjoinRoot.coe_mkₐ]

/-- The images of the two coordinate functions under an algebra homomorphism
out of the coordinate ring satisfy the Weierstrass equation of the base
change. -/
theorem equation_of_algHom {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A]
    (f : W.CoordinateRing →ₐ[F] A) :
    (W⁄A).Equation (f (AdjoinRoot.of W.polynomial X))
      (f (AdjoinRoot.root W.polynomial)) := by
  change (W.map (algebraMap F A)).Equation _ _
  rw [Affine.Equation, Affine.map_polynomial,
    ← algHom_mk_eq_evalEval f W.polynomial, AdjoinRoot.mk_self, map_zero]

/-- **Evaluation of the coordinate ring at a point of the base-changed curve.** -/
noncomputable def evalAlgHom {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A] {x y : A}
    (h : (W⁄A).Equation x y) : W.CoordinateRing →ₐ[F] A :=
  AdjoinRoot.liftAlgHom W.polynomial (Polynomial.aeval x) y <| by
    have hcoe : ((Polynomial.aeval x : F[X] →ₐ[F] A) : F[X] →+* A) =
        eval₂RingHom (algebraMap F A) x := RingHom.ext fun _ ↦ rfl
    change (W.map (algebraMap F A)).polynomial.evalEval x y = 0 at h
    rw [Affine.map_polynomial, ← eval₂_eval₂RingHom_apply] at h
    rw [hcoe]
    exact h

/-- Evaluating the class of a polynomial is polynomial evaluation at the point. -/
@[simp]
theorem evalAlgHom_mk {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A] {x y : A}
    (h : (W⁄A).Equation x y) (p : F[X][Y]) :
    evalAlgHom h (CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap F A))).evalEval x y := by
  rw [evalAlgHom, AdjoinRoot.liftAlgHom_mk]
  exact eval₂_eval₂RingHom_apply (algebraMap F A) x y p

/-- Evaluation sends the class of `X` to the first coordinate. -/
@[simp]
theorem evalAlgHom_of_X {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A] {x y : A}
    (h : (W⁄A).Equation x y) :
    evalAlgHom h (AdjoinRoot.of W.polynomial X) = x := by
  rw [← AdjoinRoot.mk_C]
  rw [evalAlgHom_mk]
  simp [evalEval_C]

/-- Evaluation sends the class of `Y` to the second coordinate. -/
@[simp]
theorem evalAlgHom_root {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A] {x y : A}
    (h : (W⁄A).Equation x y) :
    evalAlgHom h (AdjoinRoot.root W.polynomial) = y := by
  rw [← AdjoinRoot.mk_X]
  rw [evalAlgHom_mk]
  simp

end CoordinateRing

/-! ## 2. The generic point -/

/-- The generic `x`-coordinate: the class of `X` in the function field. -/
noncomputable def genericX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))

/-- The generic `y`-coordinate: the class of `Y` in the function field. -/
noncomputable def genericY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

theorem genericX_def : genericX W =
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)) := (rfl)

theorem genericY_def : genericY W =
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) := (rfl)

theorem genericX_eq_algebraMap : genericX W = algebraMap F[X] W.FunctionField X := by
  rw [genericX_def, CoordinateRing.mk_C_eq_algebraMap,
    IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]

/-- Evaluating at the generic point is reduction modulo the Weierstrass relation. -/
theorem evalEval_genericX_genericY (p : F[X][Y]) :
    (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (genericX W) (genericY W) =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p) := by
  simpa [genericX_def, genericY_def, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X]
    using (CoordinateRing.algHom_mk_eq_evalEval
      (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField) p).symm

/-- The generic coordinate functions satisfy the Weierstrass equation. -/
theorem equation_genericX_genericY :
    (W⁄W.FunctionField).Equation (genericX W) (genericY W) := by
  simpa [genericX_def, genericY_def, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X]
    using CoordinateRing.equation_of_algHom
      (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField)

/-- The generic coordinates are nonsingular on an elliptic curve. -/
theorem nonsingular_genericX_genericY [W.IsElliptic] :
    (W⁄W.FunctionField).Nonsingular (genericX W) (genericY W) := by
  letI : (W⁄W.FunctionField).IsElliptic := by
    change (W.map (algebraMap F W.FunctionField)).IsElliptic
    infer_instance
  exact equation_iff_nonsingular.mp (equation_genericX_genericY W)

/-- The generic point of `W`: the point of `W` over its own function field. -/
noncomputable def genericPoint [W.IsElliptic] : (W⁄W.FunctionField).Point :=
  Point.some (genericX W) (genericY W) (nonsingular_genericX_genericY W)

theorem genericPoint_eq_some [W.IsElliptic] : genericPoint W =
    Point.some (genericX W) (genericY W) (nonsingular_genericX_genericY W) := (rfl)

/-- The image of `F[X]` in the function field is the polynomials in `genericX`. -/
theorem algebraMap_eq_aeval_genericX (p : F[X]) :
    algebraMap F[X] W.FunctionField p = aeval (genericX W) p := by
  have h : IsScalarTower.toAlgHom F F[X] W.FunctionField = aeval (genericX W) := by
    apply Polynomial.algHom_ext
    rw [aeval_X, IsScalarTower.coe_toAlgHom', ← genericX_eq_algebraMap]
  exact congr($h p)

end WeierstrassCurve.Affine

/-! ## 3. Coordinate pullbacks and isogenies -/

namespace TauCeti

abbrev CoordinatePullback {F : Type*} [Field F]
    (W₁ W₂ : WeierstrassCurve.Affine F) : Type _ :=
  W₂.CoordinateRing →ₐ[F] W₁.FunctionField

namespace CoordinatePullback

variable {F : Type*} [Field F]

/-- The source point at infinity maps to the target point at infinity. -/
def MapsInfinity {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) : Prop :=
  letI := pullback.toRingHom.toAlgebra
  ∀ x : W₁.CoordinateRing,
    algebraMap W₁.CoordinateRing W₁.FunctionField x ∈
      integralClosure W₂.CoordinateRing W₁.FunctionField

theorem mapsInfinity_iff {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) :
    pullback.MapsInfinity ↔ ∀ x : W₁.CoordinateRing,
      @IsIntegral W₂.CoordinateRing W₁.FunctionField _ _ pullback.toRingHom.toAlgebra
        (algebraMap W₁.CoordinateRing W₁.FunctionField x) :=
  Iff.rfl

/-- A pullback maps infinity to infinity if a positive power of every source
coordinate function is pulled back from the target. -/
theorem mapsInfinity_of_pow {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) {n : ℕ} (hn : 0 < n)
    (h : ∀ z : W₁.CoordinateRing, ∃ w : W₂.CoordinateRing,
      pullback w = algebraMap W₁.CoordinateRing W₁.FunctionField z ^ n) :
    pullback.MapsInfinity := by
  rw [mapsInfinity_iff]
  let _ := pullback.toRingHom.toAlgebra
  intro z
  obtain ⟨w, hw⟩ := h z
  refine IsIntegral.of_pow hn ?_
  rw [← hw]
  rw [← AlgHom.coe_toRingHom, ← RingHom.algebraMap_toAlgebra pullback.toRingHom]
  exact isIntegral_algebraMap

/-- The identity coordinate pullback. -/
noncomputable def id (W : WeierstrassCurve.Affine F) : CoordinatePullback W W :=
  IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField

@[simp]
theorem id_apply (W : WeierstrassCurve.Affine F) (x : W.CoordinateRing) :
    id W x = algebraMap W.CoordinateRing W.FunctionField x := by
  unfold id
  exact IsScalarTower.toAlgHom_apply F W.CoordinateRing W.FunctionField x

/-- The identity pullback maps infinity to infinity. -/
@[simp]
theorem mapsInfinity_id (W : WeierstrassCurve.Affine F) :
    ∀ x : W.CoordinateRing,
      @IsIntegral W.CoordinateRing W.FunctionField _ _ (id W).toRingHom.toAlgebra
        (algebraMap W.CoordinateRing W.FunctionField x) := by
  have h : (id W).toRingHom.toAlgebra =
      (inferInstance : Algebra W.CoordinateRing W.FunctionField) := by
    apply Algebra.algebra_ext
    intro x
    rw [RingHom.algebraMap_toAlgebra]
    exact id_apply W x
  rw [h]
  exact fun _ ↦ isIntegral_algebraMap

/-- The tautological point of a coordinate pullback. -/
noncomputable def tautologicalPoint {W₁ W₂ : WeierstrassCurve.Affine F} [W₂.IsElliptic]
    (p : CoordinatePullback W₁ W₂) : (W₂⁄W₁.FunctionField).Point := by
  letI : (W₂⁄W₁.FunctionField).IsElliptic := by
    change (W₂.map (algebraMap F W₁.FunctionField)).IsElliptic
    infer_instance
  exact Point.mk (WeierstrassCurve.Affine.CoordinateRing.equation_of_algHom p)

theorem tautologicalPoint_ne_zero {W₁ W₂ : WeierstrassCurve.Affine F} [W₂.IsElliptic]
    (p : CoordinatePullback W₁ W₂) : p.tautologicalPoint ≠ 0 :=
  by
  rw [tautologicalPoint]
  exact Point.some_ne_zero _

end CoordinatePullback

/-- The pullback data of an isogeny between affine Weierstrass curves. -/
@[ext]
structure Isogeny {F : Type*} [Field F] (W₁ W₂ : WeierstrassCurve.Affine F) where
  pullback : CoordinatePullback W₁ W₂
  mapsInfinity : pullback.MapsInfinity

namespace Isogeny

variable {F : Type*} [Field F]

/-- The identity isogeny. -/
noncomputable def id (W : WeierstrassCurve.Affine F) : Isogeny W W where
  pullback := CoordinatePullback.id W
  mapsInfinity := (CoordinatePullback.mapsInfinity_iff _).2
    (CoordinatePullback.mapsInfinity_id W)

@[simp]
theorem id_pullback (W : WeierstrassCurve.Affine F) :
    (id W).pullback = CoordinatePullback.id W := (rfl)

end Isogeny

end TauCeti

/-! ## 4. Function-field division polynomials and the multiplication pullback -/

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- `ψₙ` at the generic point. -/
noncomputable def psiFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.ψ n))

/-- `ωₙ` at the generic point. -/
noncomputable def omegaFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.ω n))

/-- `φₙ` at the generic point. -/
noncomputable def phiFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.φ n))

/-- `ψcₙ` at the generic point. -/
noncomputable def psicFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.ψc n))

/-- The rational function `φₙ / ψₙ²`. -/
noncomputable def mulByIntX (n : ℤ) : W.FunctionField :=
  phiFunctionField W n / psiFunctionField W n ^ 2

/-- The rational function `ωₙ / ψₙ³`. -/
noncomputable def mulByIntY (n : ℤ) : W.FunctionField :=
  omegaFunctionField W n / psiFunctionField W n ^ 3

theorem psiFunctionField_def (n : ℤ) : psiFunctionField W n =
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.ψ n)) := (rfl)

theorem omegaFunctionField_def (n : ℤ) : omegaFunctionField W n =
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.ω n)) := (rfl)

theorem phiFunctionField_def (n : ℤ) : phiFunctionField W n =
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.φ n)) := (rfl)

theorem psicFunctionField_def (n : ℤ) : psicFunctionField W n =
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.ψc n)) := (rfl)

theorem mulByIntX_def (n : ℤ) :
    mulByIntX W n = phiFunctionField W n / psiFunctionField W n ^ 2 := (rfl)

theorem mulByIntY_def (n : ℤ) :
    mulByIntY W n = omegaFunctionField W n / psiFunctionField W n ^ 3 := (rfl)

/-- `Φₙ` at the generic point is the image of the univariate `Φₙ`. -/
theorem phiFunctionField_eq_algebraMap (n : ℤ) :
    phiFunctionField W n = algebraMap F[X] W.FunctionField (W.Φ n) := by
  rw [phiFunctionField_def, CoordinateRing.mk_φ,
    CoordinateRing.mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]

/-- `ψₙ² = ΨSqₙ` in the function field. -/
@[simp]
theorem psiFunctionField_sq (n : ℤ) : psiFunctionField W n ^ 2 =
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C (W.ΨSq n))) := by
  rw [psiFunctionField, ← map_pow, CoordinateRing.mk_ψ, CoordinateRing.mk_Ψ_sq]

/-- `ψ_{2n} = preΨ_{2n} · ψ₂` at the generic point. -/
theorem psiFunctionField_two_mul (n : ℤ) :
    psiFunctionField W (2 * n) =
      algebraMap F[X] W.FunctionField (W.preΨ (2 * n)) * psiFunctionField W 2 := by
  have h2 : psiFunctionField W 2 =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.ψ₂) := by
    rw [psiFunctionField_def, WeierstrassCurve.ψ_two]
  rw [psiFunctionField_def, CoordinateRing.mk_ψ, WeierstrassCurve.Ψ, h2]
  simp only [even_two_mul, ite_true, map_mul, CoordinateRing.mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- `Φₙ` at the generic point is `φₙ`. -/
@[simp]
theorem aeval_genericX_Φ (n : ℤ) :
    aeval (WeierstrassCurve.Affine.genericX W) (W.Φ n) = phiFunctionField W n := by
  rw [phiFunctionField_eq_algebraMap, W.algebraMap_eq_aeval_genericX]

/-- `ΨSqₙ` at the generic point is `ψₙ²`. -/
@[simp]
theorem aeval_genericX_ΨSq (n : ℤ) :
    aeval (WeierstrassCurve.Affine.genericX W) (W.ΨSq n) = psiFunctionField W n ^ 2 := by
  rw [psiFunctionField_sq, CoordinateRing.mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField,
    W.algebraMap_eq_aeval_genericX]

/-- The coordinate identity at the generic point. -/
theorem mulByIntX_mul_aeval_ΨSq (n : ℤ) (hn : psiFunctionField W n ≠ 0) :
    mulByIntX W n * aeval (WeierstrassCurve.Affine.genericX W) (W.ΨSq n) =
      aeval (WeierstrassCurve.Affine.genericX W) (W.Φ n) := by
  rw [aeval_genericX_Φ, aeval_genericX_ΨSq, mulByIntX_def]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 hn)

/-- If `ψₙ` vanishes at the generic point, then `ΨSqₙ = 0`. -/
theorem ΨSq_eq_zero_of_psiFunctionField_eq_zero {n : ℤ}
    (h : psiFunctionField W n = 0) : W.ΨSq n = 0 := by
  have hzero : algebraMap W.CoordinateRing W.FunctionField
      (CoordinateRing.mk W (C (W.ΨSq n))) = 0 := by
    rw [← psiFunctionField_sq, h, zero_pow two_ne_zero]
  rw [CoordinateRing.mk_C_eq_algebraMap] at hzero
  have h' : algebraMap F[X] W.FunctionField (W.ΨSq n) = 0 := by
    rw [IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField]
    exact hzero
  exact CoordinateRing.algebraMap_FX_functionField_injective W (by simpa using h')

/-- `ψₙ` does not vanish at the generic point when `(n : F) ≠ 0`. -/
theorem psiFunctionField_ne_zero {n : ℤ} (hn : (n : F) ≠ 0) :
    psiFunctionField W n ≠ 0 :=
  fun h ↦ W.ΨSq_ne_zero hn (ΨSq_eq_zero_of_psiFunctionField_eq_zero W h)

/-! ### The multiplication pullback and its first field -/

/-- **The source equation `equation_mulByInt`**, as a named proposition. -/
def EquationMulByInt (n : ℤ) : Prop :=
  (W⁄W.FunctionField).Equation (mulByIntX W n) (mulByIntY W n)

/-- **The coordinate pullback of `[n]`**, conditional on `EquationMulByInt`. -/
noncomputable def mulByIntPullback [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) :
    TauCeti.CoordinatePullback W W :=
  CoordinateRing.evalAlgHom h

/-- The pullback of `[n]` on a class is evaluation of a bivariate polynomial. -/
@[simp]
theorem mulByIntPullback_mk [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) (p : F[X][Y]) :
    mulByIntPullback W hn h (CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval
        (mulByIntX W n) (mulByIntY W n) :=
  CoordinateRing.evalAlgHom_mk h p

/-- The pullback of `[n]` sends the class of `X` to `φₙ/ψₙ²`. -/
@[simp]
theorem mulByIntPullback_X [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) :
    mulByIntPullback W hn h (AdjoinRoot.of W.polynomial X) = mulByIntX W n := by
  rw [← AdjoinRoot.mk_C]
  simp [mulByIntPullback]

/-- The pullback of `[n]` sends the class of `Y` to `ωₙ/ψₙ³`. -/
@[simp]
theorem mulByIntPullback_Y [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) :
    mulByIntPullback W hn h (AdjoinRoot.root W.polynomial) = mulByIntY W n := by
  rw [← AdjoinRoot.mk_X]
  simp [mulByIntPullback]

/-- **`MapsInfinity` of the multiplication pullback**, the second missing field. -/
def MapsInfinityMulByInt [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) : Prop :=
  (mulByIntPullback W hn h).MapsInfinity

/-- **Multiplication by `n` as an isogeny**, from the equation and pointedness. -/
noncomputable def mulByIntIsogeny [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n)
    (hm : MapsInfinityMulByInt W hn h) : TauCeti.Isogeny W W where
  pullback := mulByIntPullback W hn h
  mapsInfinity := hm

/-- The tautological point of the multiplication pullback. -/
noncomputable def mulByIntTautologicalPoint [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) :
    (W⁄W.FunctionField).Point :=
  (mulByIntPullback W hn h).tautologicalPoint

/-- **The source's `tautologicalPoint_mulByIntPullback`**, as a named
proposition: the tautological point of `[n]` is `n` times the generic point. -/
def TautologicalPointMulByInt [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) : Prop :=
  mulByIntTautologicalPoint W hn h = n • WeierstrassCurve.Affine.genericPoint W

/-- **The kernel of `[n]` in the point group**, Mathlib's `n`-torsion
subgroup.  This is the right-hand side of TauCeti's
`ker_mulByIntIsogeny_eq_torsionBy`; the source's translation-fixing
`Isogeny.ker` is not part of this minimal layer. -/
noncomputable def mulByIntKer [W.IsElliptic] [DecidableEq F] (n : ℤ) : AddSubgroup W.Point :=
  AddSubgroup.torsionBy W.Point n

@[simp]
theorem mem_mulByIntKer_iff [W.IsElliptic] [DecidableEq F] {n : ℤ} {P : W.Point} :
    P ∈ mulByIntKer W n ↔ n • P = 0 :=
  Submodule.mem_torsionBy_iff n P

/- The source's kernel identification `ker [n] = W.Point[n]` is the theorem
`ker_mulByIntIsogeny_eq_torsionBy`.  It is not stated as a proposition here
because the minimal `TauCeti.Isogeny` above has no `ker` field: the source
defines `ker` through the translation action on the function field, whose
fixed-field development is not part of this minimal layer.  The right-hand
side, `mulByIntKer`, is ported and is the object D5 consumes. -/

/-! ### The concrete `n = 1` instance -/

@[simp]
theorem psiFunctionField_one : psiFunctionField W 1 = 1 := by
  simp [psiFunctionField_def]

@[simp]
theorem phiFunctionField_one : phiFunctionField W 1 = WeierstrassCurve.Affine.genericX W := by
  rw [phiFunctionField_def, WeierstrassCurve.φ_one, genericX_def]

@[simp]
theorem omegaFunctionField_one :
    omegaFunctionField W 1 = WeierstrassCurve.Affine.genericY W := by
  rw [omegaFunctionField_def, WeierstrassCurve.ω_one, genericY_def]

@[simp]
theorem mulByIntX_one : mulByIntX W 1 = WeierstrassCurve.Affine.genericX W := by
  rw [mulByIntX_def, phiFunctionField_one, psiFunctionField_one]
  norm_num

@[simp]
theorem mulByIntY_one : mulByIntY W 1 = WeierstrassCurve.Affine.genericY W := by
  rw [mulByIntY_def, omegaFunctionField_one, psiFunctionField_one]
  norm_num

/-- The source equation at `n = 1`, proved. -/
theorem equationMulByInt_one : EquationMulByInt W 1 := by
  rw [EquationMulByInt, mulByIntX_one, mulByIntY_one]
  exact WeierstrassCurve.Affine.equation_genericX_genericY W

theorem psiFunctionField_one_ne_zero : psiFunctionField W 1 ≠ 0 := by
  rw [psiFunctionField_one]
  exact one_ne_zero

/-- The `n = 1` multiplication pullback is the identity pullback. -/
theorem mulByIntPullback_one [W.IsElliptic] :
    mulByIntPullback W (psiFunctionField_one_ne_zero W) (equationMulByInt_one W) =
      TauCeti.CoordinatePullback.id W := by
  refine WeierstrassCurve.Affine.CoordinateRing.algHom_ext (W := W) ?_ ?_
  · rw [mulByIntPullback_X, mulByIntX_one, TauCeti.CoordinatePullback.id_apply,
      WeierstrassCurve.Affine.genericX_def, ← AdjoinRoot.mk_C]
  · rw [mulByIntPullback_Y, mulByIntY_one, TauCeti.CoordinatePullback.id_apply,
      WeierstrassCurve.Affine.genericY_def, ← AdjoinRoot.mk_X]

/-- The `n = 1` multiplication pullback maps infinity to infinity. -/
theorem mapsInfinityMulByInt_one [W.IsElliptic] :
    MapsInfinityMulByInt W (psiFunctionField_one_ne_zero W) (equationMulByInt_one W) := by
  show (mulByIntPullback W (psiFunctionField_one_ne_zero W) (equationMulByInt_one W)).MapsInfinity
  rw [mulByIntPullback_one]
  exact (TauCeti.CoordinatePullback.mapsInfinity_iff _).2
    (TauCeti.CoordinatePullback.mapsInfinity_id W)

/-- **The concrete `[1]` isogeny**, so `mulByIntIsogeny` is inhabited. -/
noncomputable def mulByIntIsogeny_one [W.IsElliptic] : TauCeti.Isogeny W W :=
  mulByIntIsogeny W (psiFunctionField_one_ne_zero W) (equationMulByInt_one W)
    (mapsInfinityMulByInt_one W)

end TauCeti.Isogeny
