/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionField
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Torsion points, division polynomials, and algebraicity of torsion coordinates

Let `W : WeierstrassCurve K` be a Weierstrass curve over a field and let `L / K` be an
extension field.  This file addresses the gap recorded in
`IUT.ABCBridge.Galois.EllipticDivisionField`: the missing finiteness of prime-torsion
division fields, whose precise analytic input is the group-law statement

  `n • P = 0 → ψₙ(P) = 0`  (`n` odd, `P` a point of `W`),

which Mathlib does not currently provide for `n ≠ 2` (the `n = 2` case is complete in
`IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation`).

## What is proved unconditionally

* `evalDivisionPolynomialAtPoint_eq_eval_preΨ_of_odd`: for odd `n`, evaluating `ψₙ` at an
  affine point equals evaluating the univariate polynomial `preΨ n` at its `x`-coordinate.
* `divisionPolynomialDetectsTorsion_two`: the interface below holds for `n = 2`.
* `divisionPolynomialDetectsTorsion_three`: **the interface below holds for `n = 3`, in
  every characteristic.**  Proof: `3P = 0` and `P ≠ 0` give `2P = -P`, hence
  `x(2P) = x(P)` and `x(2P) = A/B` with `A = 3x² + 2a₂x + a₄ - a₁y`,
  `B = 2y + a₁x + a₃` (the doubling slope).  The doubling syzygy
  `A² + a₁AB - (a₂ + 2x)B² = Φ₂(x)`, whose verification reduces by
  `linear_combination` to the identity
  `A² + a₁AB - (a₂+2x)B² - Φ₂(x) = -(a₁² + 4a₂ + 8x)·(y² + a₁xy + a₃y - (x³ + a₂x² + a₄x + a₆))`,
  yields `x·ψ₂(x)² = x·B² = Φ₂(x) = x·Ψ₂Sq(x) - Ψ₃(x)`, so `Ψ₃(x) = 0`.

## The named interface for the general case

`DivisionPolynomialDetectsTorsion W n` is exactly the missing Mathlib statement: every
`n`-torsion point of `W` is a root of the division polynomial `ψₙ`.  All statements for
general odd `n` below are proved from this hypothesis; the file introduces no trusted
assumptions, no placeholder declaration, and no promised field.

## Algebraicity and integrality (from the interface, odd `n`, `(n : K) ≠ 0`)

* `isIntegral_of_eval₂_preΨ_eq_zero_of_odd`: a root `x` of the base change of `preΨ n` is
  integral over `K` (explicit monic witness `C ((n : K)⁻¹) * preΨ n`, monic by
  `leadingCoeff_preΨ`).
* `eval₂_preΨ_eq_zero_of_nsmul_eq_zero_of_odd`: torsion `⟹` base-changed `preΨ n` vanishes
  at the `x`-coordinate.
* `isIntegral_y_of_equation`: `IsIntegral K x` plus the Weierstrass equation gives
  `IsIntegral K y` (the monic quadratic `T² + (a₁'x + a₃')T - (x³ + a₂'x² + a₄'x + a₆')`
  over `K[x]`, then `isIntegral_trans`).
* `isIntegral_coordinates_of_nsmul_eq_zero_of_odd`: the coordinates of an `n`-torsion
  point are integral over `K`.

## Wiring into the division field (consumer unchanged)

`IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity.hasIntegralCoordinates_of_torsion`
provides `EllipticDivisionField.HasIntegralCoordinates K L E Q` for an `n`-torsion point
`Q` of `E⁄L`, and `pointField_finiteDimensional_of_torsion` /
`divisionField_finiteDimensional_of_torsion` feed it into the existing finiteness theorems
of `EllipticDivisionField`.  The consumer's environment hypothesis
`HasIntegralCoordinates` is thereby replaced, for odd `n` with `(n : K) ≠ 0`, by the
explicit bridge hypothesis `DivisionPolynomialDetectsTorsion (E⁄L) n`.

## PARKED gaps (explicitly not claimed)

* Even `n ≥ 4`: no bridge instance is provided here.
* `char K ∣ n`: the monic scaling `C ((n : K)⁻¹) * preΨ n` degenerates; all integrality
  statements carry `(n : K) ≠ 0`.
* The unconditional odd-`n` bridge is not claimed.  Three routes were investigated and
  blocked on missing Mathlib infrastructure:
  (a) coordinate ring: `mk_ψ`/`mk_φ`/`mk_Ψ_sq` exist, but the coordinate formula
  `x([n]P) = φₙ/ψₙ²` needs the bivariate `ωₙ`, which is not defined in Mathlib (TODO in
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`), and there is no
  divisor theory for the coordinate ring;
  (b) elliptic nets: `normEDS` recurrences exist, but Mathlib has not proved that
  `normEDS` is an elliptic divisibility sequence (TODO in
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`), and there is no bridge from nets
  to points;
  (c) direct `nsmul` coordinate formulas on `Affine.Point` do not exist (only two-point
  `slope`/`addX` case formulas).

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point, division field
-/

open Polynomial

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- For odd `n`, evaluating `ψₙ` at a point is evaluating the univariate polynomial
`preΨ n` at its `x`-coordinate. -/
theorem evalDivisionPolynomialAtPoint_eq_eval_preΨ_of_odd {n : ℤ} (hn : ¬ Even n)
    {x y : R} (h : W.toAffine.Nonsingular x y) :
    W.evalDivisionPolynomialAtPoint n (WeierstrassCurve.Affine.Point.some x y h) =
      (W.preΨ n).eval x := by
  rw [evalDivisionPolynomialAtPoint_some, W.evalDivisionPolynomial_eq_eval_preΨ_of_odd h.1 hn]

end CommRing

section Field

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The missing Mathlib torsion bridge, as a named interface.**

`DivisionPolynomialDetectsTorsion W n` states that every `n`-torsion point of `W` is a
root of the `n`-division polynomial `ψₙ`, expressed through the evaluation function
`evalDivisionPolynomialAtPoint`.  For `n = 2` this is Mathlib-supported (proved in
`EllipticDivisionPolynomialEvaluation`), for `n = 3` it is proved below, and for general
odd `n` it is the precise gap this file does not close: the coordinate formula
`x([n]P) = φₙ/ψₙ²` requires the bivariate polynomials `ωₙ`, which are not available in
Mathlib. -/
def DivisionPolynomialDetectsTorsion (W : WeierstrassCurve F) (n : ℤ) : Prop :=
  ∀ P : W.toAffine.Point, n • P = 0 → W.evalDivisionPolynomialAtPoint n P = 0

/-- The interface holds at `n = 2`: the two-torsion computation of
`EllipticDivisionPolynomialEvaluation`. -/
theorem divisionPolynomialDetectsTorsion_two (W : WeierstrassCurve F) :
    DivisionPolynomialDetectsTorsion W 2 := by
  intro P hP
  have hP' : (2 : ℕ) • P = 0 := by
    rwa [show (2 : ℤ) • P = (2 : ℕ) • P from natCast_zsmul P 2] at hP
  exact (W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero P).mp hP'

/-- **The `3`-torsion bridge, unconditionally and in every characteristic.**  A point
`P` with `3 • P = 0` is a root of the `3`-division polynomial.  The proof uses the
doubling syzygy `x(2P) = φ₂(x)/ψ₂(x)²`, verified against the Weierstrass equation. -/
theorem evalDivisionPolynomialAtPoint_three_eq_zero_of_three_nsmul_eq_zero (W : WeierstrassCurve F)
    (P : W.toAffine.Point) (hP : (3 : ℕ) • P = 0) :
    W.evalDivisionPolynomialAtPoint 3 P = 0 := by
  have h3 : P + P + P = 0 := by
    rw [show (3 : ℕ) • P = P + P + P by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]] at hP
    exact hP
  cases P with
  | zero => rw [evalDivisionPolynomialAtPoint_zero]
  | some x y hns =>
      rw [evalDivisionPolynomialAtPoint_some,
        W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 (by decide : ¬ Even (3 : ℤ))]
      set A : F := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hA
      set B : F := 2 * y + W.a₁ * x + W.a₃ with hB
      have hPP_ne : WeierstrassCurve.Affine.Point.some x y hns +
          WeierstrassCurve.Affine.Point.some x y hns ≠ 0 := by
        intro h2
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns (by
          have h := h3
          rw [h2, zero_add] at h
          exact h)
      have h2P : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hns ≠ 0 := by
        rwa [two_nsmul]
      have hpsi2 : W.evalDivisionPolynomialAtPoint 2
          (WeierstrassCurve.Affine.Point.some x y hns) ≠ 0 :=
        fun h0 => h2P ((W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero _).mpr h0)
      have hB_ne : B ≠ 0 := by
        intro h0
        exact hpsi2 (by
          rw [evalDivisionPolynomialAtPoint_some, W.evalDivisionPolynomial_two, ← hB]
          exact h0)
      have hy_ne : y ≠ W.toAffine.negY x y := by
        intro hy
        exact hpsi2 (by
          rw [evalDivisionPolynomialAtPoint_some]
          exact W.evalDivisionPolynomial_two_eq_zero_iff_negY.mpr hy)
      have h2P_neg : WeierstrassCurve.Affine.Point.some x y hns +
          WeierstrassCurve.Affine.Point.some x y hns =
            -WeierstrassCurve.Affine.Point.some x y hns :=
        (add_eq_zero_iff_eq_neg).mp h3
      have hX : W.toAffine.addX x x (W.toAffine.slope x x y y) = x :=
        (WeierstrassCurve.Affine.Point.some.inj
          ((WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_ne).symm.trans
            (h2P_neg.trans (WeierstrassCurve.Affine.Point.neg_some hns)))).1
      have hslope : W.toAffine.slope x x y y = A / B := by
        have hy' : ¬y = -y - W.a₁ * x - W.a₃ := by
          simpa only [WeierstrassCurve.Affine.negY] using hy_ne
        rw [WeierstrassCurve.Affine.slope_of_Y_ne' hy', hA, hB]
        ring
      have hXAB : W.toAffine.addX x x (A / B) = x := by
        rw [← hslope]
        exact hX
      have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
          (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
        (WeierstrassCurve.Affine.equation_iff' (W := W.toAffine) x y).mp hns.1
      have hPhi : (W.Φ 2).eval x = A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 := by
        rw [hA, hB, WeierstrassCurve.Φ_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
          WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        linear_combination (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * hE
      have hPsi2Sq : (W.Ψ₂Sq).eval x = B ^ 2 := by
        rw [hB, WeierstrassCurve.Ψ₂Sq]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C,
          WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
        linear_combination (-4) * hE
      have hsplit : W.Ψ₃.eval x = x * (W.Ψ₂Sq).eval x - (W.Φ 2).eval x := by
        rw [WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Φ_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat]
        ring
      have hXB : A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 = x * B ^ 2 := by
        have h : W.toAffine.addX x x (A / B) * B ^ 2 =
            A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 := by
          simp only [WeierstrassCurve.Affine.addX]
          field_simp [hB_ne]
          ring
        rw [← h, hXAB]
      rw [WeierstrassCurve.preΨ_three, hsplit, hPsi2Sq, hPhi, hXB]
      exact sub_self _

/-- The interface holds at `n = 3` in every characteristic (from ℕ-scalar to ℤ-scalar). -/
theorem divisionPolynomialDetectsTorsion_three (W : WeierstrassCurve F) :
    DivisionPolynomialDetectsTorsion W 3 := by
  intro P hP
  exact W.evalDivisionPolynomialAtPoint_three_eq_zero_of_three_nsmul_eq_zero P (by
    rwa [show (3 : ℤ) • P = (3 : ℕ) • P from natCast_zsmul P 3] at hP)

end Field

section Extension

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Monic witness for the `x`-coordinate.**  If `x` is a root of the base change of
`preΨ n` for odd `n` with `(n : K) ≠ 0`, then `x` is integral over `K`: the polynomial
`C ((n : K)⁻¹) * preΨ n` is monic because `leadingCoeff_preΨ` identifies the leading
coefficient with `(n : K)` in the odd case. -/
theorem isIntegral_of_eval₂_preΨ_eq_zero_of_odd (W : WeierstrassCurve K) {n : ℤ} (hodd : ¬ Even n)
    (hne : (n : K) ≠ 0) {x : L} (hx : (W.preΨ n).eval₂ (algebraMap K L) x = 0) :
    IsIntegral K x := by
  refine ⟨C ((n : K)⁻¹) * W.preΨ n, ?_, ?_⟩
  · refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [W.leadingCoeff_preΨ hne, if_neg hodd]
    exact inv_mul_cancel₀ hne
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hx, mul_zero]

/-- **The `y`-coordinate is integral.**  If `(x, y)` satisfies the Weierstrass equation
of `W⁄L` and `x` is integral over `K`, then so is `y`: `y` is a root of the monic
quadratic `T² + (a₁'x + a₃')T - (x³ + a₂'x² + a₄'x + a₆')` with coefficients in
`Algebra.adjoin K {x}`, which is integral over `K`. -/
theorem isIntegral_y_of_equation (W : WeierstrassCurve K) {x y : L}
    (h : (W.baseChange L).toAffine.Equation x y) (hx : IsIntegral K x) : IsIntegral K y := by
  have h' : y ^ 2 + algebraMap K L W.a₁ * x * y + algebraMap K L W.a₃ * y =
      x ^ 3 + algebraMap K L W.a₂ * x ^ 2 + algebraMap K L W.a₄ * x + algebraMap K L W.a₆ := by
    have h'' := (WeierstrassCurve.Affine.equation_iff (W := (W.baseChange L).toAffine) x y).mp h
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using h''
  let S : Subalgebra K L := Algebra.adjoin K ({x} : Set L)
  have hxS : x ∈ S := Algebra.subset_adjoin rfl
  have hSint : Algebra.IsIntegral K S :=
    (le_integralClosure_iff_isIntegral (S := S)).mp (adjoin_le_integralClosure hx)
  let c₁ : S := ⟨algebraMap K L W.a₁ * x + algebraMap K L W.a₃, by
    exact S.add_mem (S.mul_mem (S.algebraMap_mem W.a₁) hxS) (S.algebraMap_mem W.a₃)⟩
  let c₀ : S := ⟨-(x ^ 3 + algebraMap K L W.a₂ * x ^ 2 + algebraMap K L W.a₄ * x +
      algebraMap K L W.a₆), by
    exact S.neg_mem (S.add_mem (S.add_mem (S.add_mem (S.pow_mem hxS 3)
      (S.mul_mem (S.algebraMap_mem W.a₂) (S.pow_mem hxS 2)))
      (S.mul_mem (S.algebraMap_mem W.a₄) hxS)) (S.algebraMap_mem W.a₆))⟩
  let q : S[X] := X ^ 2 + (C c₁ * X + C c₀)
  have hq_monic : q.Monic := by
    have h1 : (C c₁ * X : S[X]).degree ≤ (1 : WithBot ℕ) := by
      calc (C c₁ * X : S[X]).degree
          ≤ (C c₁ : S[X]).degree + (X : S[X]).degree := Polynomial.degree_mul_le _ _
        _ ≤ (0 : WithBot ℕ) + 1 := add_le_add Polynomial.degree_C_le Polynomial.degree_X_le
        _ = 1 := zero_add 1
    have h0 : (C c₀ : S[X]).degree ≤ (0 : WithBot ℕ) := Polynomial.degree_C_le
    refine Polynomial.monic_X_pow_add ?_
    calc (C c₁ * X + C c₀ : S[X]).degree
        ≤ max (C c₁ * X : S[X]).degree (C c₀ : S[X]).degree := Polynomial.degree_add_le _ _
      _ ≤ max (1 : WithBot ℕ) 0 := max_le_max h1 h0
      _ < (2 : WithBot ℕ) := by norm_num
  have hq_eval : eval₂ (algebraMap S L) y q = 0 := by
    have hqmap : q.map (algebraMap S L) = X ^ 2 + (C (algebraMap K L W.a₁ * x +
        algebraMap K L W.a₃) * X + C (-(x ^ 3 + algebraMap K L W.a₂ * x ^ 2 +
        algebraMap K L W.a₄ * x + algebraMap K L W.a₆))) := by
      have h₁ : algebraMap S L c₁ = algebraMap K L W.a₁ * x + algebraMap K L W.a₃ := rfl
      have h₀ : algebraMap S L c₀ = -(x ^ 3 + algebraMap K L W.a₂ * x ^ 2 +
          algebraMap K L W.a₄ * x + algebraMap K L W.a₆) := rfl
      simp only [q, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C, h₁, h₀]
    rw [Polynomial.eval₂_eq_eval_map, hqmap]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    linear_combination h'
  haveI := hSint
  exact isIntegral_trans y ⟨q, hq_monic, hq_eval⟩

/-- **Torsion gives a root of `preΨ n`.**  Under the bridge interface, an `n`-torsion
point has `x`-coordinate satisfying the base-changed `preΨ n`. -/
theorem eval₂_preΨ_eq_zero_of_nsmul_eq_zero_of_odd (W : WeierstrassCurve K) [DecidableEq L]
    {n : ℤ} (hbridge : DivisionPolynomialDetectsTorsion (W.baseChange L) n) (hodd : ¬ Even n)
    {x y : L} (hns : (W.baseChange L).toAffine.Nonsingular x y)
    (hP : n • WeierstrassCurve.Affine.Point.some x y hns = 0) :
    (W.preΨ n).eval₂ (algebraMap K L) x = 0 := by
  have h0 : (W.baseChange L).evalDivisionPolynomialAtPoint n
      (WeierstrassCurve.Affine.Point.some x y hns) = 0 := hbridge _ hP
  rw [evalDivisionPolynomialAtPoint_some,
    (W.baseChange L).evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd] at h0
  have hmap : (W.preΨ n).map (algebraMap K L) = (W.baseChange L).preΨ n := by
    change (W.preΨ n).map (algebraMap K L) = (W.map (algebraMap K L)).preΨ n
    rw [WeierstrassCurve.map_preΨ]
  rw [Polynomial.eval₂_eq_eval_map, hmap]
  exact h0

/-- **Coordinates of odd-torsion points are integral** (from the bridge interface). -/
theorem isIntegral_coordinates_of_nsmul_eq_zero_of_odd (W : WeierstrassCurve K) [DecidableEq L]
    {n : ℤ} (hbridge : DivisionPolynomialDetectsTorsion (W.baseChange L) n) (hodd : ¬ Even n)
    (hne : (n : K) ≠ 0) {x y : L} (hns : (W.baseChange L).toAffine.Nonsingular x y)
    (hP : n • WeierstrassCurve.Affine.Point.some x y hns = 0) :
    IsIntegral K x ∧ IsIntegral K y := by
  have hx : IsIntegral K x :=
    isIntegral_of_eval₂_preΨ_eq_zero_of_odd W hodd hne
      (eval₂_preΨ_eq_zero_of_nsmul_eq_zero_of_odd W hbridge hodd hns hP)
  exact ⟨hx, isIntegral_y_of_equation W hns.1 hx⟩

end Extension

end WeierstrassCurve

namespace IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity

open WeierstrassCurve

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- **Wiring to `EllipticDivisionField`.**  Coordinates of an `n`-torsion point of
`E⁄L` are integral over `K`, i.e. `HasIntegralCoordinates K L E Q`, given the bridge
interface for `E⁄L` and `(n : K) ≠ 0`. -/
theorem hasIntegralCoordinates_of_torsion (E : WeierstrassCurve.Affine K)
    (Q : (WeierstrassCurve.Affine.baseChange E L).Point) {n : ℤ} [DecidableEq L]
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) n)
    (hodd : ¬ Even n) (hne : (n : K) ≠ 0) (hQ : n • Q = 0) :
    EllipticDivisionField.HasIntegralCoordinates K L E Q := by
  cases Q with
  | zero =>
      intro z hz
      have hz' : z ∈ (∅ : Set L) := hz
      exact (Set.notMem_empty z hz').elim
  | some x y hns =>
      have hxy := E.isIntegral_coordinates_of_nsmul_eq_zero_of_odd hbridge hodd hne hns hQ
      intro z hz
      rw [EllipticDivisionField.pointCoordinateSet_some] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxy.1
      · exact hxy.2

/-- The coordinate field of a single odd-torsion point is finite-dimensional over `K`
(from the bridge interface). -/
theorem pointField_finiteDimensional_of_torsion (E : WeierstrassCurve.Affine K)
    (Q : (WeierstrassCurve.Affine.baseChange E L).Point) {n : ℤ} [DecidableEq L]
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) n)
    (hodd : ¬ Even n) (hne : (n : K) ≠ 0) (hQ : n • Q = 0) :
    FiniteDimensional K ↥(EllipticDivisionField.pointField K L E Q) :=
  EllipticDivisionField.pointField_finiteDimensional K L E Q
    (hasIntegralCoordinates_of_torsion K L E Q hbridge hodd hne hQ)

/-- The division field of a finite family of odd-torsion points is finite-dimensional
over `K` (from the bridge interface). -/
theorem divisionField_finiteDimensional_of_torsion (E : WeierstrassCurve.Affine K) {ι : Type*}
    [Finite ι] (P : ι → (WeierstrassCurve.Affine.baseChange E L).Point) {n : ℤ} [DecidableEq L]
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) n)
    (hodd : ¬ Even n) (hne : (n : K) ≠ 0) (hP : ∀ i, n • P i = 0) :
    FiniteDimensional K ↥(EllipticDivisionField.divisionField K L E P) :=
  EllipticDivisionField.divisionField_finiteDimensional K L E P fun i =>
    hasIntegralCoordinates_of_torsion K L E (P i) hbridge hodd hne (hP i)

end IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity
