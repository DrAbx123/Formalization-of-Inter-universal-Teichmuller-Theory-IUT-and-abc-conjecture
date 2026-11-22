/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import tmp.sheaf.xif.paper.S1467FunctionFieldPullbackActual
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Algebra.Module.Torsion.Basic

/-! # S1483: TauCeti multiplication-by-n on the function field, on S1467 generic layer

S1467 is the unique generic/function-field layer: it supplies genericX, genericY,
genericPoint, equation_genericX_genericY, Point.map, map_genericPoint_injective,
CoordinatePullback, MapsInfinity, Isogeny, fieldPullback.  This file imports it
and does NOT redefine any of those names.

It ports the remaining TauCeti `Isogeny/MulByInt/Basic.lean` objects:
psi/omega/phi/psic at the generic point, mulByIntX/Y, EquationMulByInt,
`mulByIntPullback`, `mulByIntIsogeny`, the tautological point, and the
torsionBy kernel object.  `EquationMulByInt` and `MapsInfinityMulByInt` are
the exact first fields; they are explicit arguments, not axioms.

The source `Isogeny.ker` (translation fixed field) is not part of the S1467
minimal Isogeny, so the kernel equality is recorded on the actual torsionBy
subgroup, not fabricated as a field of Isogeny.

Provenance: TauCeti `AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Basic.lean`
(Apache-2.0), adapted to Mathlib v4.32.2. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace CoordinateRing

/-- Evaluation of the coordinate ring at a point of the base-changed curve. -/
noncomputable def evalAlgHom {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A] {x y : A}
    (h : (W⁄A).Equation x y) : W.CoordinateRing →ₐ[F] A :=
  AdjoinRoot.liftAlgHom W.polynomial (Polynomial.aeval x) y <| by
    have hcoe : ((Polynomial.aeval x : F[X] →ₐ[F] A) : F[X] →+* A) =
        eval₂RingHom (algebraMap F A) x := RingHom.ext fun _ ↦ rfl
    change (W.map (algebraMap F A)).polynomial.evalEval x y = 0 at h
    rw [Affine.map_polynomial, ← eval₂_eval₂RingHom_apply] at h
    rw [hcoe]
    exact h

@[simp] theorem evalAlgHom_mk {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A] {x y : A}
    (h : (W⁄A).Equation x y) (p : F[X][Y]) :
    evalAlgHom h (CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap F A))).evalEval x y := by
  rw [evalAlgHom, AdjoinRoot.liftAlgHom_mk]
  exact eval₂_eval₂RingHom_apply (algebraMap F A) x y p

@[simp] theorem evalAlgHom_of_X {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A] {x y : A}
    (h : (W⁄A).Equation x y) :
    evalAlgHom h (AdjoinRoot.of W.polynomial X) = x := by
  rw [← AdjoinRoot.mk_C]
  rw [evalAlgHom_mk]
  simp [evalEval_C]

@[simp] theorem evalAlgHom_root {W : WeierstrassCurve.Affine F} {A : Type*} [CommRing A] [Algebra F A] {x y : A}
    (h : (W⁄A).Equation x y) :
    evalAlgHom h (AdjoinRoot.root W.polynomial) = y := by
  rw [← AdjoinRoot.mk_X]
  rw [evalAlgHom_mk]
  simp

/-- Two algebra homomorphisms out of the coordinate ring agreeing on the two
coordinate functions are equal. -/
@[ext] theorem algHom_ext {W : WeierstrassCurve.Affine F} {A : Type*} [Semiring A] [Algebra F A]
    {f g : W.CoordinateRing →ₐ[F] A}
    (hX : f (AdjoinRoot.of W.polynomial X) = g (AdjoinRoot.of W.polynomial X))
    (hY : f (AdjoinRoot.root W.polynomial) = g (AdjoinRoot.root W.polynomial)) :
    f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    simpa using hX
  · exact hY

/-- The image of `F[X]` in the function field is the polynomials in genericX. -/
theorem algebraMap_eq_aeval_genericX (p : F[X]) :
    algebraMap F[X] W.FunctionField p = aeval (genericX W) p := by
  have h : IsScalarTower.toAlgHom F F[X] W.FunctionField = aeval (genericX W) := by
    apply Polynomial.algHom_ext
    rw [aeval_X, IsScalarTower.coe_toAlgHom', ← genericX_eq_algebraMap]
  exact congr($h p)

end CoordinateRing

end WeierstrassCurve.Affine

namespace TauCeti

open WeierstrassCurve.Affine

namespace CoordinatePullback

variable {F : Type*} [Field F]

/-- The identity coordinate pullback. -/
noncomputable def id (W : WeierstrassCurve.Affine F) : CoordinatePullback W W :=
  IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField

@[simp] theorem id_apply (W : WeierstrassCurve.Affine F) (x : W.CoordinateRing) :
    id W x = algebraMap W.CoordinateRing W.FunctionField x := by
  unfold id
  exact IsScalarTower.toAlgHom_apply F W.CoordinateRing W.FunctionField x

theorem mapsInfinity_id (W : WeierstrassCurve.Affine F) :
    (id W).MapsInfinity := by
  rw [mapsInfinity_iff]
  intro x
  have h : (id W).toRingHom.toAlgebra =
      (inferInstance : Algebra W.CoordinateRing W.FunctionField) := by
    apply Algebra.algebra_ext
    intro y
    rw [RingHom.algebraMap_toAlgebra]
    exact id_apply W y
  rw [h]
  exact isIntegral_algebraMap

/-- The tautological point of a coordinate pullback. -/
noncomputable def tautologicalPoint {W1 W2 : WeierstrassCurve.Affine F} [W2.IsElliptic]
    (p : CoordinatePullback W1 W2) : (W2⁄W1.FunctionField).Point := by
  letI : (W2⁄W1.FunctionField).IsElliptic := by
    change (W2.map (algebraMap F W1.FunctionField)).IsElliptic
    infer_instance
  exact Point.mk (WeierstrassCurve.Affine.CoordinateRing.equation_of_algHom W2 p)

theorem tautologicalPoint_ne_zero {W1 W2 : WeierstrassCurve.Affine F} [W2.IsElliptic]
    (p : CoordinatePullback W1 W2) : p.tautologicalPoint ≠ 0 := by
  rw [tautologicalPoint]
  exact Point.some_ne_zero _

end CoordinatePullback

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
  rw [phiFunctionField_eq_algebraMap, CoordinateRing.algebraMap_eq_aeval_genericX W]

/-- `ΨSqₙ` at the generic point is `ψₙ²`. -/
@[simp]
theorem aeval_genericX_ΨSq (n : ℤ) :
    aeval (WeierstrassCurve.Affine.genericX W) (W.ΨSq n) = psiFunctionField W n ^ 2 := by
  rw [psiFunctionField_sq, CoordinateRing.mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField,
    CoordinateRing.algebraMap_eq_aeval_genericX W]

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
  exact CoordinateRing.algebraMap_FX_injective W (by simpa using h')

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

/-- The actual kernel object is Mathlib's `n`-torsion subgroup; this is the
right-hand side of TauCeti's `ker_mulByIntIsogeny_eq_torsionBy`. -/
theorem mulByIntKer_eq_torsionBy [W.IsElliptic] [DecidableEq F] (n : ℤ) :
    mulByIntKer W n = AddSubgroup.torsionBy W.Point n := rfl

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

