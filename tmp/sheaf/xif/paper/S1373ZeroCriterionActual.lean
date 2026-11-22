/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity

/-!
# The division-polynomial zero criterion, unconditionally for `n = 3`

Let `W` be a Weierstrass curve over a field `F`, and let `ψₙ` be the `n`-division polynomial of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial`.  The **zero criterion** is

  `ψₙ(P) = 0 ↔ n • P = 0`  for every point `P` of `W`,

equivalently, the divisor of `ψₙ` on `W` is supported exactly on the `n`-torsion subgroup:
`div(ψₙ) = n²(O) - Σ_{T ∈ E[n]} T`.

This file proves the criterion **unconditionally for `n = 2` and `n = 3`, in every
characteristic of the base field**, and records the general criterion as the predicate
`WeierstrassCurve.DivisionPolynomialZeroCriterion`.  For `n ≥ 4` the general statement is *not*
claimed here: Mathlib v4.32.2 has no group-law bridge from `ψₙ` to `n • P`, no bivariate `ωₙ`,
and no divisor theory on the coordinate ring of `W`.  The `n = 3` proof below is an exact first
lemma towards that general target: it closes the converse direction `ψ₃(P) = 0 → 3 • P = 0`
(the forward direction `3 • P = 0 → ψ₃(P) = 0` was already proved in
`IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity` in every characteristic).

## The `n = 3` proof

Write `P = (x, y)`, and define the doubling numerator and denominator

* `A = 3x² + 2a₂x + a₄ - a₁y`,
* `B = 2y + a₁x + a₃ = ψ₂(x, y)`.

On the curve one has the syzygies

* `Φ₂(x) = A² + a₁AB - (a₂ + 2x)B²`,
* `Ψ₂Sq(x) = B²`,
* `Ψ₃(x) = x Ψ₂Sq(x) - Φ₂(x)`.

If `B = 0`, then `Φ₂(x) = A²` and `Ψ₃(x) = -A²`; the vanishing of `Ψ₃(x)` forces `A = 0`,
contradicting nonsingularity of `(x, y)` (both partial derivatives would vanish).  Hence a root of
`ψ₃` has `B ≠ 0`.  In that case the doubling formula gives
`x(2P) = (A² + a₁AB - (a₂ + 2x)B²)/B² = x`, so `2P = P` or `2P = -P`; the first is impossible for
a nonzero point, and the second gives `3P = 0`.  This argument is purely algebraic and does not
use any hypothesis on the characteristic.

## Main results

* `WeierstrassCurve.DivisionPolynomialZeroCriterion`: the general zero-criterion predicate.
* `WeierstrassCurve.DivisionPolynomialRootsAreTorsion`: its converse/root half.
* `WeierstrassCurve.divisionPolynomialZeroCriterion_two`.
* `WeierstrassCurve.three_nsmul_eq_zero_of_evalDivisionPolynomialAtPoint_three_eq_zero`.
* `WeierstrassCurve.three_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_three_eq_zero`.
* `WeierstrassCurve.divisionPolynomialZeroCriterion_three`.
* `WeierstrassCurve.rootSet_two_eq_torsion`, `WeierstrassCurve.rootSet_three_eq_torsion`:
  the root set of `ψ₂`/`ψ₃` is exactly the torsion subgroup (the support part of the divisor
  identity above).

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point, zero criterion
-/

open Polynomial

namespace WeierstrassCurve

section Field

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- **The division-polynomial zero criterion at `n`.**  Every point is `n`-torsion exactly when
the `n`-division polynomial vanishes there.  This is the pointwise (support) form of the divisor
identity `div(ψₙ) = n²(O) - Σ_{T ∈ E[n]} T`. -/
def DivisionPolynomialZeroCriterion (n : ℤ) : Prop :=
  ∀ P : W.toAffine.Point, n • P = 0 ↔ W.evalDivisionPolynomialAtPoint n P = 0

/-- The root half of the zero criterion: every root of `ψₙ` is `n`-torsion.  This is the
converse of the interface `DivisionPolynomialDetectsTorsion` from
`IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity`. -/
def DivisionPolynomialRootsAreTorsion (n : ℤ) : Prop :=
  ∀ P : W.toAffine.Point, W.evalDivisionPolynomialAtPoint n P = 0 → n • P = 0

/-- The zero criterion is exactly the conjunction of the two one-sided interfaces. -/
theorem divisionPolynomialZeroCriterion_iff_detects (n : ℤ) :
    W.DivisionPolynomialZeroCriterion n ↔
      DivisionPolynomialDetectsTorsion W n ∧ W.DivisionPolynomialRootsAreTorsion n := by
  constructor
  · intro h
    exact ⟨fun P hP => (h P).mp hP, fun P hP => (h P).mpr hP⟩
  · rintro ⟨hdet, hroot⟩ P
    exact ⟨hdet P, hroot P⟩

/-- **`n = 2` zero criterion.**  A point is `2`-torsion exactly when `ψ₂` vanishes there.  This is
the Mathlib-supported group-law case (`ψ₂ = 2Y + a₁X + a₃`). -/
theorem divisionPolynomialZeroCriterion_two : W.DivisionPolynomialZeroCriterion 2 := by
  intro P
  rw [show (2 : ℤ) • P = (2 : ℕ) • P from natCast_zsmul P 2]
  exact W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero P

/-- The root half of the zero criterion at `n = 2`. -/
theorem divisionPolynomialRootsAreTorsion_two : W.DivisionPolynomialRootsAreTorsion 2 :=
  ((W.divisionPolynomialZeroCriterion_iff_detects 2).mp
    W.divisionPolynomialZeroCriterion_two).2

/-- **The root half of the zero criterion at `n = 3`, in every characteristic.**  If the
`3`-division polynomial vanishes at a point `P`, then `3 • P = 0`.

The proof is the computation described in the module docstring: with `A` and `B` as above,
`B = 0` is impossible at a root of `Ψ₃` by nonsingularity, while `B ≠ 0` makes the doubling
`x`-coordinate equal to `x`, so `2P = ±P` and the non-trivial alternative gives `3P = 0`. -/
theorem three_nsmul_eq_zero_of_evalDivisionPolynomialAtPoint_three_eq_zero
    (P : W.toAffine.Point)
    (hpsi : W.evalDivisionPolynomialAtPoint 3 P = 0) : (3 : ℤ) • P = 0 := by
  cases P with
  | zero => exact zsmul_zero 3
  | some x y hns =>
    rw [evalDivisionPolynomialAtPoint_some,
      W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 (by decide : ¬ Even (3 : ℤ)),
      W.preΨ_three] at hpsi
    set A : F := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hA
    set B : F := 2 * y + W.a₁ * x + W.a₃ with hB
    have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
        (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
      (WeierstrassCurve.Affine.equation_iff' (W := W.toAffine) x y).mp hns.1
    have hPhi : (W.Φ 2).eval x = A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 := by
      rw [hA, hB, WeierstrassCurve.Φ_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C,
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
    by_cases hB0 : B = 0
    · -- If `B = 0` then `Φ₂(x) = A²` and `Ψ₃(x) = -A²`, so `A = 0`; both partial
      -- derivatives vanish, contradicting nonsingularity.
      have hA2 : A ^ 2 = 0 := by
        have hPhi0 : (W.Φ 2).eval x = 0 := by
          have h := hpsi
          rw [hsplit, hPsi2Sq, hB0] at h
          linear_combination -h
        rw [hPhi, hB0] at hPhi0
        simpa using hPhi0
      have hA0 : A = 0 := by simpa using hA2
      have hPX : W.toAffine.polynomialX.evalEval x y = 0 := by
        rw [WeierstrassCurve.Affine.evalEval_polynomialX]
        rw [hA] at hA0
        linear_combination -hA0
      have hPY : W.toAffine.polynomialY.evalEval x y = 0 := by
        rw [WeierstrassCurve.Affine.evalEval_polynomialY]
        rw [hB] at hB0
        exact hB0
      rcases hns.2 with hX | hY
      · exact (hX hPX).elim
      · exact (hY hPY).elim
    · -- If `B ≠ 0`, the doubling `x`-coordinate is `x`, so `2P = ±P`.
      have hB2 : B ^ 2 ≠ 0 := pow_ne_zero 2 hB0
      have hXB : A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 = x * B ^ 2 := by
        have h := hpsi
        rw [hsplit, hPsi2Sq, hPhi] at h
        linear_combination -h
      have hslope : W.toAffine.slope x x y y = A / B := by
        have hy' : ¬ y = -y - W.a₁ * x - W.a₃ := by
          intro h
          apply hB0
          rw [hB]
          linear_combination h
        rw [WeierstrassCurve.Affine.slope_of_Y_ne' hy', hA, hB]
        ring
      have hXformula : W.toAffine.addX x x (A / B) * B ^ 2 =
          A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 := by
        simp only [WeierstrassCurve.Affine.addX]
        field_simp [hB0]
        ring
      have hX : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
        rw [hslope]
        apply mul_right_cancel₀ hB2
        rw [hXformula]
        exact hXB
      have hy_ne : y ≠ W.toAffine.negY x y := by
        intro h
        apply hB0
        rw [hB, WeierstrassCurve.Affine.negY] at *
        linear_combination h
      let x' : F := W.toAffine.addX x x (W.toAffine.slope x x y y)
      let y' : F := W.toAffine.addY x x y (W.toAffine.slope x x y y)
      let h' : W.toAffine.Nonsingular x' y' :=
        W.toAffine.nonsingular_add hns hns fun hxy => hy_ne hxy.right
      have hx' : x' = x := hX
      have hYor : y' = y ∨ y' = W.toAffine.negY x y :=
        WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 hns.1 hx'
      have h2Peq : WeierstrassCurve.Affine.Point.some x y hns +
          WeierstrassCurve.Affine.Point.some x y hns =
            WeierstrassCurve.Affine.Point.some x' y' h' :=
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_ne
      rcases hYor with hy | hy
      · -- `2P = P` would force `P = 0`, impossible for an affine point.
        have h2P : WeierstrassCurve.Affine.Point.some x y hns +
            WeierstrassCurve.Affine.Point.some x y hns =
              WeierstrassCurve.Affine.Point.some x y hns := by
          rw [h2Peq]
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx', hy⟩
        have hP0 : WeierstrassCurve.Affine.Point.some x y hns = 0 := by
          have h := h2P
          have h' : WeierstrassCurve.Affine.Point.some x y hns +
              WeierstrassCurve.Affine.Point.some x y hns =
                WeierstrassCurve.Affine.Point.some x y hns + 0 := by
            rw [h, add_zero]
          exact add_left_cancel h'
        exact absurd hP0 (WeierstrassCurve.Affine.Point.some_ne_zero hns)
      · -- `2P = -P` gives `3P = 0`.
        have h2P : WeierstrassCurve.Affine.Point.some x y hns +
            WeierstrassCurve.Affine.Point.some x y hns =
              -WeierstrassCurve.Affine.Point.some x y hns := by
          rw [h2Peq, WeierstrassCurve.Affine.Point.neg_some]
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx', hy⟩
        have h3P : (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hns = 0 := by
          rw [show (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hns =
              (WeierstrassCurve.Affine.Point.some x y hns +
                WeierstrassCurve.Affine.Point.some x y hns) +
                WeierstrassCurve.Affine.Point.some x y hns by
            rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]]
          rw [h2P]
          exact neg_add_cancel _
        rwa [show (3 : ℤ) • WeierstrassCurve.Affine.Point.some x y hns =
          (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hns from
            natCast_zsmul _ 3]

/-- The root half of the zero criterion at `n = 3`. -/
theorem divisionPolynomialRootsAreTorsion_three : W.DivisionPolynomialRootsAreTorsion 3 :=
  W.three_nsmul_eq_zero_of_evalDivisionPolynomialAtPoint_three_eq_zero

/-- **The `n = 3` zero criterion, in every characteristic.**  A point is `3`-torsion exactly when
the `3`-division polynomial vanishes at it.  This is the support statement of
`div(ψ₃) = 9(O) - Σ_{T ∈ E[3]} T`. -/
theorem three_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_three_eq_zero
    (P : W.toAffine.Point) :
    (3 : ℤ) • P = 0 ↔ W.evalDivisionPolynomialAtPoint 3 P = 0 := by
  constructor
  · intro hP
    refine W.evalDivisionPolynomialAtPoint_three_eq_zero_of_three_nsmul_eq_zero P ?_
    rwa [show (3 : ℤ) • P = (3 : ℕ) • P from natCast_zsmul P 3] at hP
  · exact W.three_nsmul_eq_zero_of_evalDivisionPolynomialAtPoint_three_eq_zero P

/-- The zero criterion at `n = 3`, packaged as `DivisionPolynomialZeroCriterion`. -/
theorem divisionPolynomialZeroCriterion_three : W.DivisionPolynomialZeroCriterion 3 :=
  W.three_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_three_eq_zero

/-- Coordinate form of the `n = 3` zero criterion for a nonsingular affine point. -/
theorem evalDivisionPolynomial_three_eq_zero_iff_three_nsmul_eq_zero {x y : F}
    (hns : W.toAffine.Nonsingular x y) :
    W.evalDivisionPolynomial x y 3 = 0 ↔
      (3 : ℤ) • WeierstrassCurve.Affine.Point.some x y hns = 0 := by
  change W.evalDivisionPolynomialAtPoint 3
    (WeierstrassCurve.Affine.Point.some x y hns) = 0 ↔ _
  exact (W.three_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_three_eq_zero _).symm

/-- The root set of `ψ₂` is exactly the `2`-torsion subgroup (support part of the divisor
identity for `ψ₂`). -/
theorem rootSet_two_eq_torsion :
    {P : W.toAffine.Point | W.evalDivisionPolynomialAtPoint 2 P = 0} =
      {P : W.toAffine.Point | (2 : ℤ) • P = 0} := by
  ext P
  exact (W.divisionPolynomialZeroCriterion_two P).symm

/-- The root set of `ψ₃` is exactly the `3`-torsion subgroup, in every characteristic (support
part of the divisor identity for `ψ₃`). -/
theorem rootSet_three_eq_torsion :
    {P : W.toAffine.Point | W.evalDivisionPolynomialAtPoint 3 P = 0} =
      {P : W.toAffine.Point | (3 : ℤ) • P = 0} := by
  ext P
  exact (W.divisionPolynomialZeroCriterion_three P).symm

end Field

end WeierstrassCurve
