/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# Evaluation of division polynomials at affine points

Let `W` be a Weierstrass curve over a commutative ring `R`.  This file studies the honest,
library-available interaction between the division polynomials `ψₙ`, `φₙ`, `Ψₙ`, `Φₙ` of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial` and actual points of the affine
curve `W.toAffine`.

The two facts that Mathlib provides are
* `CoordinateRing.mk_ψ`, `CoordinateRing.mk_φ` and `CoordinateRing.mk_Ψ_sq`, expressing the
  congruence of the division polynomials in the coordinate ring `R[W]`, and
* `AdjoinRoot.evalEval_mk`, the universal property that evaluation at a solution `(x, y)` of the
  Weierstrass equation factors through the coordinate ring.

Combining them yields, for every solution `(x, y)` of `W` and every `n : ℤ`,
`ψₙ(x, y) = Ψₙ(x, y)`, and for odd `n` the sharper statement `ψₙ(x, y) = preΨₙ(x)` that the
odd division polynomial depends only on the `x`-coordinate.  The latter is the geometric content
of "the odd `n`-division polynomial is a function of `x`", i.e. it is constant on the pair
`{P, -P}`.

Mathlib does **not** contain the group-law correspondence `n • P = 0 ↔ ψₙ(P) = 0` for general `n`,
and we do not assume it.  The one genuine `nsmul` relation that the library supports is at `n = 2`:
a point is `2`-torsion exactly when its `y`-coordinate equals `negY x y`, which is exactly the
vanishing of the `2`-division polynomial `ψ₂ = 2Y + a₁X + a₃`.  This is proved below as
`two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero`.

## Main definitions

* `WeierstrassCurve.evalDivisionPolynomial`: evaluation of `ψₙ` at affine coordinates.
* `WeierstrassCurve.evalDivisionPolynomialAtPoint`: evaluation of `ψₙ` at a point.

## Main results

* `WeierstrassCurve.evalDivisionPolynomial_eq_evalEval_Ψ`: `ψₙ(x, y) = Ψₙ(x, y)`.
* `WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd`: for odd `n`, `ψₙ(x, y) = preΨₙ(x)`.
* `WeierstrassCurve.evalEval_φ_eq_eval_Φ`: `φₙ(x, y) = Φₙ(x)`.
* `WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq`: `Ψₙ(x, y)² = ΨSqₙ(x)`.
* `WeierstrassCurve.evalDivisionPolynomialAtPoint_neg_of_odd`: for odd `n`, `ψₙ(-P) = ψₙ(P)`.
* `WeierstrassCurve.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

open Polynomial
open scoped Polynomial.Bivariate

universe u

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The evaluation of the bivariate `n`-division polynomial `ψₙ` at affine coordinates `(x, y)`.

This is a plain polynomial evaluation; the point of the file is to show that, whenever `(x, y)` is
a solution of the Weierstrass equation of `W`, this value is the same as the evaluation of the
congruent polynomial `Ψₙ`, and that for odd `n` it only depends on `x`. -/
noncomputable def evalDivisionPolynomial (x y : R) (n : ℤ) : R :=
  Polynomial.evalEval x y (W.ψ n)

@[simp]
lemma evalDivisionPolynomial_zero (x y : R) : W.evalDivisionPolynomial x y 0 = 0 := by
  simp [evalDivisionPolynomial]

@[simp]
lemma evalDivisionPolynomial_one (x y : R) : W.evalDivisionPolynomial x y 1 = 1 := by
  simp [evalDivisionPolynomial]

@[simp]
lemma evalDivisionPolynomial_neg (x y : R) (n : ℤ) :
    W.evalDivisionPolynomial x y (-n) = -W.evalDivisionPolynomial x y n := by
  simp [evalDivisionPolynomial]

/-- The value of the `2`-division polynomial `ψ₂ = 2Y + a₁X + a₃` at `(x, y)`. -/
@[simp]
lemma evalDivisionPolynomial_two (x y : R) :
    W.evalDivisionPolynomial x y 2 = 2 * y + W.a₁ * x + W.a₃ := by
  rw [evalDivisionPolynomial, ψ_two, ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY]

/-- **Congruence in the coordinate ring evaluated at a solution.**
For every solution `(x, y)` of the Weierstrass equation of `W` and every `n : ℤ`, the bivariate
division polynomial `ψₙ` and the polynomial `Ψₙ` (which is built from `preΨₙ` and `ψ₂`) take the
same value at `(x, y)`.  This is `CoordinateRing.mk_ψ` pushed through the evaluation homomorphism
`AdjoinRoot.evalEval`. -/
theorem evalDivisionPolynomial_eq_evalEval_Ψ {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    W.evalDivisionPolynomial x y n = Polynomial.evalEval x y (W.Ψ n) := by
  have h0 : Polynomial.evalEval x y W.toAffine.polynomial = 0 := h
  change Polynomial.evalEval x y (W.ψ n) = Polynomial.evalEval x y (W.Ψ n)
  calc Polynomial.evalEval x y (W.ψ n)
      = (AdjoinRoot.evalEval h0) (AdjoinRoot.mk W.toAffine.polynomial (W.ψ n)) :=
        (AdjoinRoot.evalEval_mk h0 (W.ψ n)).symm
    _ = (AdjoinRoot.evalEval h0) (AdjoinRoot.mk W.toAffine.polynomial (W.Ψ n)) := by
        rw [WeierstrassCurve.Affine.CoordinateRing.mk_ψ]
    _ = Polynomial.evalEval x y (W.Ψ n) := AdjoinRoot.evalEval_mk h0 (W.Ψ n)

/-- For odd `n`, the polynomial `Ψₙ` is the univariate polynomial `preΨₙ` in the `x`-coordinate. -/
lemma Ψ_eq_C_preΨ_of_odd {n : ℤ} (hn : ¬ Even n) : W.Ψ n = C (W.preΨ n) := by
  rw [WeierstrassCurve.Ψ, if_neg hn, mul_one]

/-- **Odd division polynomials only see the `x`-coordinate.**
For every solution `(x, y)` of the Weierstrass equation of `W` and every odd `n : ℤ`, the value
`ψₙ(x, y)` equals the value of the univariate polynomial `preΨₙ` at `x`. -/
theorem evalDivisionPolynomial_eq_eval_preΨ_of_odd {x y : R} (h : W.toAffine.Equation x y)
    {n : ℤ} (hn : ¬ Even n) :
    W.evalDivisionPolynomial x y n = (W.preΨ n).eval x := by
  rw [W.evalDivisionPolynomial_eq_evalEval_Ψ h n, Ψ_eq_C_preΨ_of_odd W hn, Polynomial.evalEval_C]

/-- For odd `n`, the `n`-division polynomial takes the same value at `(x, y)` and at the opposite
point `(x, negY x y)` of the curve.  This is the coordinate form of `ψₙ(P) = ψₙ(-P)`. -/
theorem evalDivisionPolynomial_negY_of_odd {x y : R} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : ¬ Even n) :
    W.evalDivisionPolynomial x (W.toAffine.negY x y) n = W.evalDivisionPolynomial x y n := by
  rw [W.evalDivisionPolynomial_eq_eval_preΨ_of_odd ((W.toAffine.equation_neg x y).mpr h.1) hn,
    W.evalDivisionPolynomial_eq_eval_preΨ_of_odd h.1 hn]

/-- For even `n`, the polynomial `Ψₙ` is `preΨₙ` times the `2`-division polynomial `ψ₂`. -/
lemma Ψ_eq_C_preΨ_mul_ψ₂_of_even {n : ℤ} (hn : Even n) :
    W.Ψ n = C (W.preΨ n) * W.ψ₂ := by
  rw [WeierstrassCurve.Ψ, if_pos hn]

/-- The `2`-division polynomial `ψ₂` changes sign at the opposite point `(x, negY x y)`. -/
theorem evalEval_ψ₂_negY (x y : R) :
    Polynomial.evalEval x (W.toAffine.negY x y) W.ψ₂ = -Polynomial.evalEval x y W.ψ₂ := by
  rw [ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.Affine.evalEval_polynomialY, WeierstrassCurve.Affine.negY]
  ring

/-- For even `n`, the `n`-division polynomial changes sign at the opposite point
`(x, negY x y)`.  Together with `evalDivisionPolynomial_negY_of_odd` this is the full statement
`ψₙ(-P) = ±ψₙ(P)`. -/
theorem evalDivisionPolynomial_negY_of_even {x y : R} (h : W.toAffine.Equation x y)
    {n : ℤ} (hn : Even n) :
    W.evalDivisionPolynomial x (W.toAffine.negY x y) n = -W.evalDivisionPolynomial x y n := by
  rw [W.evalDivisionPolynomial_eq_evalEval_Ψ ((W.toAffine.equation_neg x y).mpr h) n,
    W.evalDivisionPolynomial_eq_evalEval_Ψ h n, Ψ_eq_C_preΨ_mul_ψ₂_of_even W hn]
  simp only [Polynomial.evalEval_mul, Polynomial.evalEval_C, evalEval_ψ₂_negY]
  ring

/-- **The congruent polynomial `φₙ` evaluated at a solution.**
For every solution `(x, y)` of the Weierstrass equation of `W` and every `n : ℤ`, the bivariate
polynomial `φₙ` and the univariate polynomial `Φₙ` take the same value at `(x, y)`. -/
theorem evalEval_φ_eq_eval_Φ {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    Polynomial.evalEval x y (W.φ n) = (W.Φ n).eval x := by
  have h0 : Polynomial.evalEval x y W.toAffine.polynomial = 0 := h
  calc Polynomial.evalEval x y (W.φ n)
      = (AdjoinRoot.evalEval h0) (AdjoinRoot.mk W.toAffine.polynomial (W.φ n)) :=
        (AdjoinRoot.evalEval_mk h0 (W.φ n)).symm
    _ = (AdjoinRoot.evalEval h0)
          (AdjoinRoot.mk W.toAffine.polynomial (C (W.Φ n))) := by
        rw [WeierstrassCurve.Affine.CoordinateRing.mk_φ]
    _ = Polynomial.evalEval x y (C (W.Φ n)) := AdjoinRoot.evalEval_mk h0 (C (W.Φ n))
    _ = (W.Φ n).eval x := Polynomial.evalEval_C x y (W.Φ n)

/-- **The square of `Ψₙ` evaluated at a solution.**
For every solution `(x, y)` of the Weierstrass equation of `W` and every `n : ℤ`, the square of
`Ψₙ(x, y)` equals the value of the univariate polynomial `ΨSqₙ` at `x`. -/
theorem evalEval_Ψ_sq_eq_eval_ΨSq {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (Polynomial.evalEval x y (W.Ψ n)) ^ 2 = (W.ΨSq n).eval x := by
  have h0 : Polynomial.evalEval x y W.toAffine.polynomial = 0 := h
  have h2 := congrArg (AdjoinRoot.evalEval h0)
    (WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq W n)
  simp only [map_pow, AdjoinRoot.evalEval_mk, Polynomial.evalEval_C] at h2
  exact h2

/-- The evaluation of `ψₙ` at a point of `W`, read off from the affine coordinates of the
constructor of the point.  The value at the point at infinity is set to `0`. -/
noncomputable def evalDivisionPolynomialAtPoint (n : ℤ) : W.toAffine.Point → R
  | .zero => 0
  | .some x y _ => W.evalDivisionPolynomial x y n

@[simp]
lemma evalDivisionPolynomialAtPoint_zero (n : ℤ) :
    W.evalDivisionPolynomialAtPoint n WeierstrassCurve.Affine.Point.zero = 0 := rfl

@[simp]
lemma evalDivisionPolynomialAtPoint_some (x y : R) (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    W.evalDivisionPolynomialAtPoint n (WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y n := rfl

/-- For odd `n`, the evaluation of `ψₙ` at a point does not change under negation: the odd
division polynomial is constant on the pair `{P, -P}`. -/
theorem evalDivisionPolynomialAtPoint_neg_of_odd {n : ℤ} (hn : ¬ Even n)
    (P : W.toAffine.Point) :
    W.evalDivisionPolynomialAtPoint n (-P) = W.evalDivisionPolynomialAtPoint n P := by
  cases P with
  | zero =>
      have hneg : -WeierstrassCurve.Affine.Point.zero = WeierstrassCurve.Affine.Point.zero :=
        WeierstrassCurve.Affine.Point.neg_zero (W' := W.toAffine)
      rw [hneg]
  | some x y h =>
      rw [WeierstrassCurve.Affine.Point.neg_some, evalDivisionPolynomialAtPoint_some,
        evalDivisionPolynomialAtPoint_some,
        W.evalDivisionPolynomial_eq_eval_preΨ_of_odd ((W.toAffine.equation_neg x y).mpr h.1) hn,
        W.evalDivisionPolynomial_eq_eval_preΨ_of_odd h.1 hn]

/-- For even `n`, the evaluation of `ψₙ` changes sign under negation. -/
theorem evalDivisionPolynomialAtPoint_neg_of_even {n : ℤ} (hn : Even n)
    (P : W.toAffine.Point) :
    W.evalDivisionPolynomialAtPoint n (-P) = -W.evalDivisionPolynomialAtPoint n P := by
  cases P with
  | zero =>
      have hneg : -WeierstrassCurve.Affine.Point.zero = WeierstrassCurve.Affine.Point.zero :=
        WeierstrassCurve.Affine.Point.neg_zero (W' := W.toAffine)
      rw [hneg, evalDivisionPolynomialAtPoint_zero, neg_zero]
  | some x y h =>
      rw [WeierstrassCurve.Affine.Point.neg_some, evalDivisionPolynomialAtPoint_some,
        evalDivisionPolynomialAtPoint_some]
      exact W.evalDivisionPolynomial_negY_of_even h.1 hn

end CommRing

section Field

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

/-- The `2`-division polynomial `ψ₂` vanishes at `(x, y)` exactly when `y` is the other root
`negY x y` of the Weierstrass equation, i.e. exactly when `(x, y)` is `2`-torsion. -/
theorem evalDivisionPolynomial_two_eq_zero_iff_negY {x y : F} :
    W.evalDivisionPolynomial x y 2 = 0 ↔ y = W.toAffine.negY x y := by
  rw [evalDivisionPolynomial_two, WeierstrassCurve.Affine.negY]
  change (2 * y + W.a₁ * x + W.a₃ = 0) ↔ (y = -y - W.a₁ * x - W.a₃)
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

variable [DecidableEq F]

/-- **The genuine `nsmul` relation available for torsion points.**
A point `P = (x, y)` of `W` is `2`-torsion, i.e. `2 • P = 0`, exactly when the `2`-division
polynomial vanishes at its coordinates.  This is the only `nsmul`-torsion relation for which
Mathlib supplies the group-law correspondence; the analogous statement for odd primes is *not*
available in the library and is not assumed here. -/
theorem two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y h = 0 ↔
      W.evalDivisionPolynomial x y 2 = 0 := by
  rw [evalDivisionPolynomial_two_eq_zero_iff_negY, two_nsmul]
  constructor
  · intro h2
    have h2' : WeierstrassCurve.Affine.Point.some x y h =
        -WeierstrassCurve.Affine.Point.some x y h := (add_eq_zero_iff_eq_neg).mp h2
    rw [WeierstrassCurve.Affine.Point.neg_some] at h2'
    exact (WeierstrassCurve.Affine.Point.some.inj h2').2
  · intro hy
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy

/-- The point-level form of `two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero`:
`2 • P = 0` if and only if the `2`-division polynomial vanishes at `P`. -/
theorem two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero
    (P : W.toAffine.Point) :
    (2 : ℕ) • P = 0 ↔ W.evalDivisionPolynomialAtPoint 2 P = 0 := by
  cases P with
  | zero =>
      have h0 : W.evalDivisionPolynomialAtPoint 2 WeierstrassCurve.Affine.Point.zero = 0 :=
        W.evalDivisionPolynomialAtPoint_zero 2
      rw [h0]
      exact iff_of_true (nsmul_zero (M := W.toAffine.Point) 2) rfl
  | some x y h =>
      simpa using W.two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero h

end Field

end WeierstrassCurve
