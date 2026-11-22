import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

/-!
# S1372: the general x-coordinate formula and the exact first Mathlib gap

For a Weierstrass curve `W` over a field `K` and a nonsingular affine point
`P = (x, y)`, the standard formula for the x-coordinate of the integer multiple
`n • P` is

  x(n • P) = Φₙ(x) / ψₙ(x, y) ^ 2,   provided ψₙ(x, y) ≠ 0,

where `Φₙ` is Mathlib's univariate `WeierstrassCurve.Φ n` and `ψₙ` is
Mathlib's bivariate `WeierstrassCurve.ψ n`.

This file records the precise reduction and the exact first missing lemma.

## What is proved here, without axioms or sorry

1. The predicate `S1372XCoordinateFormula W n` is exactly the target formula.
2. The formula holds for `n = 1` and `n = 2` (the `n = 2` proof is the
   tangent-slope computation, reproduced here without importing any
   sorry-bearing file).
3. The formula is invariant under `n ↦ -n`; hence proving it for all
   positive `n` proves it for all `n`.
4. The `n = 2` formula implies the forward division-polynomial detection at
   `n = 2` (the already-known Mathlib case).
5. The full `n + 1` induction step is proved as
   `xCoordinateFormula_step`: if the formula is known at `n - 1` and
   `n - 2`, if all `ψ_k` for `1 ≤ k ≤ n + 1` are nonzero, and if the
   point-level omega identity holds at `n - 1`, then the formula holds at
   `n`.  Combined with `xCoordinateFormula_one` and
   `xCoordinateFormula_two`, this reduces the general theorem exactly to the
   two missing inputs below.

## The exact first missing lemma

The standard proof for general `n` is an induction on `n` using the affine
addition formula and the two division-polynomial recurrences
`ψ_even` and `ψ_odd`.  It requires two facts that Mathlib 4.32.2 does not
provide:

* `S1372EllipticNetAtPoint W x y`: the sequence `n ↦ ψₙ(x, y)` is an
  elliptic net (equivalently, it satisfies the elliptic relation
  `ER(p,q,r,s) = 0` for all integers `p,q,r,s`).  Mathlib has the definition
  `IsEllipticNet` and the recurrences of `normEDS`, but the theorem
  `IsEllipticNet (normEDS b c d)` is an explicit TODO in
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.  This is exactly
  the bridge from the `normEDS` recurrences to the point-level sequence.

* `S1372OmegaFormula W n`: the y-coordinate formula
  `y(n • P) = ωₙ(x,y) / ψₙ(x,y) ^ 3`, where the bivariate `ωₙ` is not
  defined in Mathlib (the declaration `WeierstrassCurve.ω` is an explicit
  TODO in `DivisionPolynomial/Basic.lean`).  A local `ω` can be written
  down from `ψ_{2n}`, `φₙ` and `ψₙ`; the missing content is the identity
  `2 y(nP) + a₁ x(nP) + a₃ = ψ_{2n}(P) / ψₙ(P) ^ 4`, which is the
  point-level input of the induction.

Both statements are propositions, not axioms.  Nothing in this file assumes
them, and no `sorry`, `admit`, `axiom` or `opaque` declaration is used.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual

open Polynomial
open LeanFormal.IUT
open WeierstrassCurve

/-! ## 1. The target formula -/

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-- The x-coordinate of an affine point, none at infinity. -/
noncomputable def xCoord : W.Point → Option K
  | .zero => none
  | .some x _ _ => some x

@[simp]
lemma xCoord_zero : xCoord W (0 : W.Point) = none := rfl

@[simp]
lemma xCoord_some {x y : K} (h : W.Nonsingular x y) :
    xCoord W (WeierstrassCurve.Affine.Point.some x y h) = some x := rfl

/-- The value of the bivariate `2`-division polynomial at a point: this is
`2y + a₁x + a₃` on an affine point and `0` at infinity.  It is the
quantity that the point-level omega identity controls. -/
noncomputable def wCoord : W.Point → K
  | .zero => 0
  | .some x y _ => 2 * y + W.a₁ * x + W.a₃

@[simp]
lemma wCoord_zero : wCoord W (0 : W.Point) = 0 := rfl

@[simp]
lemma wCoord_some {x y : K} (h : W.Nonsingular x y) :
    wCoord W (WeierstrassCurve.Affine.Point.some x y h) =
      2 * y + W.a₁ * x + W.a₃ := rfl

/-- The evaluated even `ψ`-recurrence at an affine point. -/
lemma evalDivisionPolynomial_even {x y : K} (h : W.Nonsingular x y) (m : ℤ) :
    W.evalDivisionPolynomial x y (2 * m) * W.evalDivisionPolynomial x y 2 =
      W.evalDivisionPolynomial x y (m - 1) ^ 2 *
          W.evalDivisionPolynomial x y m * W.evalDivisionPolynomial x y (m + 2) -
        W.evalDivisionPolynomial x y (m - 2) * W.evalDivisionPolynomial x y m *
          W.evalDivisionPolynomial x y (m + 1) ^ 2 := by
  have h := congrArg (Polynomial.evalEval x y) (W.ψ_even m)
  simpa [WeierstrassCurve.evalDivisionPolynomial] using h

/-- The evaluated odd `ψ`-recurrence at an affine point. -/
lemma evalDivisionPolynomial_odd {x y : K} (h : W.Nonsingular x y) (m : ℤ) :
    W.evalDivisionPolynomial x y (2 * m + 1) =
      W.evalDivisionPolynomial x y (m + 2) * W.evalDivisionPolynomial x y m ^ 3 -
        W.evalDivisionPolynomial x y (m - 1) * W.evalDivisionPolynomial x y (m + 1) ^ 3 := by
  have h := congrArg (Polynomial.evalEval x y) (W.ψ_odd m)
  simpa [WeierstrassCurve.evalDivisionPolynomial] using h

/-- Evaluation of `Φₘ` at a point in terms of `ψ`. -/
lemma phi_eval {x y : K} (h : W.Nonsingular x y) (m : ℤ) :
    (W.Φ m).eval x =
      x * (W.evalDivisionPolynomial x y m) ^ 2 -
        W.evalDivisionPolynomial x y (m + 1) * W.evalDivisionPolynomial x y (m - 1) := by
  have hphi := WeierstrassCurve.evalEval_φ_eq_eval_Φ W h.1 m
  rw [show x * (W.evalDivisionPolynomial x y m) ^ 2 -
        W.evalDivisionPolynomial x y (m + 1) * W.evalDivisionPolynomial x y (m - 1)
      = Polynomial.evalEval x y (W.φ m) by
    simp [WeierstrassCurve.φ, WeierstrassCurve.evalDivisionPolynomial, Polynomial.evalEval,
      mul_comm]]
  exact hphi.symm

/-- The addition-law recurrence for the x-coordinate, in the form used by the
division-polynomial induction.  For `Q = (u, v)` with `u ≠ x`,
`x(P + Q) = x(P - Q) - ψ₂(P) ψ₂(Q) / (u - x) ^ 2`. -/
lemma xCoord_recurrence {x y u v : K} (hP : W.Nonsingular x y) (hQ : W.Nonsingular u v)
    (hx : u ≠ x) :
    xCoord W (WeierstrassCurve.Affine.Point.some x y hP +
        WeierstrassCurve.Affine.Point.some u v hQ) =
      some (W.addX x u (W.slope x u y v)) ∧
    xCoord W (WeierstrassCurve.Affine.Point.some x y hP -
        WeierstrassCurve.Affine.Point.some u v hQ) =
      some (W.addX x u (W.slope x u y (W.negY u v))) ∧
    W.addX x u (W.slope x u y v) =
      W.addX x u (W.slope x u y (W.negY u v)) -
        (2 * y + W.a₁ * x + W.a₃) * (2 * v + W.a₁ * u + W.a₃) / (u - x) ^ 2 := by
  constructor
  · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx.symm, xCoord_some]
  constructor
  · have hne : x ≠ u := hx.symm
    have hsub : WeierstrassCurve.Affine.Point.some x y hP -
        WeierstrassCurve.Affine.Point.some u v hQ =
        WeierstrassCurve.Affine.Point.some x y hP +
          (-WeierstrassCurve.Affine.Point.some u v hQ) := by rw [sub_eq_add_neg]
    rw [hsub, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.add_of_X_ne hne, xCoord_some]
  · rw [WeierstrassCurve.Affine.addX_eq_addX_negY_sub y v hx.symm]
    have h1 : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
      rw [WeierstrassCurve.Affine.negY]; ring
    have h2 : v - W.negY u v = 2 * v + W.a₁ * u + W.a₃ := by
      rw [WeierstrassCurve.Affine.negY]; ring
    rw [h1, h2]

/-- **The target of S1372.**  Away from the zeros of `ψₙ`, the x-coordinate
of `n • P` is `Φₙ(x) / ψₙ(x,y) ^ 2`. -/
def S1372XCoordinateFormula (n : ℤ) : Prop :=
  ∀ (x y : K) (h : W.Nonsingular x y),
    W.evalDivisionPolynomial x y n ≠ 0 →
      xCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
        some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2)

section Generic

/-- The formula is invariant under `n ↦ -n`: `(-n) • P = -(n • P)`, the
x-coordinate is unchanged by negation, `Φₙ` is even, and `ψₙ` changes only
by sign, so its square is unchanged. -/
theorem xCoordinateFormula_neg (n : ℤ) :
    S1372XCoordinateFormula W n → S1372XCoordinateFormula W (-n) := by
  intro h x y hns hne
  have hne_n : W.evalDivisionPolynomial x y n ≠ 0 := by
    intro h0
    exact hne (by simpa [W.evalDivisionPolynomial_neg] using congrArg Neg.neg h0)
  have hP := h x y hns hne_n
  have hneg : (-n) • (WeierstrassCurve.Affine.Point.some x y hns) =
      -(n • WeierstrassCurve.Affine.Point.some x y hns) := by
    rw [neg_smul]
  rw [hneg]
  cases hQ : n • (WeierstrassCurve.Affine.Point.some x y hns) with
  | zero =>
      rw [hQ] at hP
      simp [xCoord] at hP
  | some x' y' h' =>
      rw [hQ] at hP
      have hx' : x' = (W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2 := by
        simpa [xCoord] using hP
      rw [WeierstrassCurve.Affine.Point.neg_some, xCoord_some]
      rw [hx']
      congr 1
      rw [WeierstrassCurve.Φ_neg, W.evalDivisionPolynomial_neg]
      ring

/-- The formula is invariant under `n ↦ -n`. -/
theorem xCoordinateFormula_neg_iff (n : ℤ) :
    S1372XCoordinateFormula W n ↔ S1372XCoordinateFormula W (-n) :=
  ⟨xCoordinateFormula_neg W n,
    fun h => by simpa using xCoordinateFormula_neg W (-n) h⟩

/-- The formula at `n = 1` is immediate. -/
theorem xCoordinateFormula_one : S1372XCoordinateFormula W 1 := by
  intro x y h hne
  simp

/-- The formula at `n = 2`, from the tangent-slope formula.  This is the
first nontrivial case and is proved unconditionally. -/
theorem xCoordinateFormula_two : S1372XCoordinateFormula W 2 := by
  intro x y h hne
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (WeierstrassCurve.Affine.equation_iff' (W := W) x y).mp h.1
  have hB : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    simpa [WeierstrassCurve.evalDivisionPolynomial_two] using hne
  have hy : y ≠ W.negY x y := by
    intro hy
    exact hne ((WeierstrassCurve.evalDivisionPolynomial_two_eq_zero_iff_negY (W := W)).mpr hy)
  set A : K := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hA
  set B : K := 2 * y + W.a₁ * x + W.a₃ with hBdef
  have hBne : B ≠ 0 := by simpa [hBdef] using hB
  have hslope : W.slope x x y y = A / B := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    rw [WeierstrassCurve.Affine.negY]
    simp only [hA, hBdef]
    congr 1
    ring
  have hpoly : A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 -
      (W.Φ 2).eval x =
      (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x)) *
        (y ^ 2 + W.a₁ * x * y + W.a₃ * y -
          (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
    rw [hA, hBdef, WeierstrassCurve.Φ_two]
    simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hAB : W.addX x x (A / B) * B ^ 2 =
      A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 := by
    rw [WeierstrassCurve.Affine.addX]
    field_simp [hBne]
    ring
  have hmain : W.addX x x (A / B) * B ^ 2 - (W.Φ 2).eval x = 0 := by
    rw [hAB, hpoly, hE]
    ring
  have hformula : W.addX x x (A / B) = (W.Φ 2).eval x / B ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hBne)]
    linear_combination hmain
  rw [two_zsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  rw [xCoord_some, WeierstrassCurve.evalDivisionPolynomial_two]
  rw [hslope, hformula]

/-- The formula at `n = 2` implies forward detection at `n = 2`. -/
theorem detection_two_of_xCoordinateFormula_two :
    ∀ P : W.Point, (2 : ℤ) • P = 0 → W.evalDivisionPolynomialAtPoint 2 P = 0 := by
  intro P hP
  cases P with
  | zero => simp
  | some x y h =>
      by_contra hne
      have hx := xCoordinateFormula_two W x y h hne
      rw [hP] at hx
      simp [xCoord] at hx

lemma xCoord_neg (P : W.Point) : xCoord W (-P) = xCoord W P := by
  cases P with
  | zero => rfl
  | some x y h => rw [WeierstrassCurve.Affine.Point.neg_some, xCoord_some, xCoord_some]

/-- One step of the division-polynomial induction for the x-coordinate. -/
theorem xCoordinateFormula_step
    (n : ℤ) (hn3 : 3 ≤ n) (x y : K) (h : W.Nonsingular x y)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0)
    (hxm1 : xCoord W ((n - 1) • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2))
    (hxm2 : xCoord W ((n - 2) • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ (n - 2)).eval x / (W.evalDivisionPolynomial x y (n - 2)) ^ 2))
    (hω : wCoord W ((n - 1) • WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y (2 * (n - 1)) /
        (W.evalDivisionPolynomial x y (n - 1)) ^ 4) :
    xCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2) := by
  let P0 : W.Point := WeierstrassCurve.Affine.Point.some x y h
  have hn1 : (1 : ℤ) ≤ n := by linarith
  have hψ_n : W.evalDivisionPolynomial x y n ≠ 0 := hψ n hn1 (by linarith)
  have hψ_nm1 : W.evalDivisionPolynomial x y (n - 1) ≠ 0 := hψ (n - 1) (by linarith) (by linarith)
  have hψ_nm2 : W.evalDivisionPolynomial x y (n - 2) ≠ 0 := hψ (n - 2) (by linarith) (by linarith)
  have hψ_np1 : W.evalDivisionPolynomial x y (n + 1) ≠ 0 := hψ (n + 1) (by linarith) (by linarith)
  rcases hQ : ((n - 1) • P0) with _ | ⟨u, v, hQns⟩
  · rw [hQ] at hxm1
    simp [xCoord] at hxm1
  · rw [hQ] at hxm1 hω
    have hu : u = (W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2 := by
      simpa [xCoord] using hxm1
    have hwQ : 2 * v + W.a₁ * u + W.a₃ =
        W.evalDivisionPolynomial x y (2 * (n - 1)) /
          (W.evalDivisionPolynomial x y (n - 1)) ^ 4 := by
      simpa [wCoord] using hω
    have hphi_nm1 := phi_eval W h (n - 1)
    have hphi_nm1' : (W.Φ (n - 1)).eval x =
        x * (W.evalDivisionPolynomial x y (n - 1)) ^ 2 -
          W.evalDivisionPolynomial x y n * W.evalDivisionPolynomial x y (n - 2) := by
      simpa [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] using hphi_nm1
    have hux : u ≠ x := by
      intro hux
      have h0 : W.evalDivisionPolynomial x y n * W.evalDivisionPolynomial x y (n - 2) = 0 := by
        have h1 : u - x = 0 := sub_eq_zero.mpr hux
        rw [hu, hphi_nm1'] at h1
        field_simp [hψ_nm1] at h1
        linear_combination -h1
      exact mul_ne_zero hψ_n hψ_nm2 h0
    rcases hR : ((n - 2) • P0) with _ | ⟨s, t, hRns⟩
    · rw [hR] at hxm2
      simp [xCoord] at hxm2
    · rw [hR] at hxm2
      have hs : s = (W.Φ (n - 2)).eval x / (W.evalDivisionPolynomial x y (n - 2)) ^ 2 := by
        simpa [xCoord] using hxm2
      have hrec := xCoord_recurrence W h hQns hux
      have hplus : P0 + WeierstrassCurve.Affine.Point.some u v hQns = n • P0 := by
        rw [← hQ]
        calc P0 + (n - 1) • P0 = (1 : ℤ) • P0 + (n - 1) • P0 := by rw [one_zsmul]
          _ = (1 + (n - 1)) • P0 := (add_zsmul (m := (1 : ℤ)) (n := n - 1) P0).symm
          _ = n • P0 := by rw [show 1 + (n - 1) = n by ring]
      have hminus : P0 - WeierstrassCurve.Affine.Point.some u v hQns = -( (n - 2) • P0) := by
        rw [← hQ, sub_eq_add_neg, ← neg_zsmul]
        calc P0 + ((- (n - 1)) • P0) = (1 : ℤ) • P0 + ((- (n - 1)) • P0) := by rw [one_zsmul]
          _ = (1 + (- (n - 1))) • P0 := (add_zsmul (m := (1 : ℤ)) (n := - (n - 1)) P0).symm
          _ = (2 - n) • P0 := by rw [show 1 + (- (n - 1)) = 2 - n by ring]
          _ = -( (n - 2) • P0) := by rw [show 2 - n = -(n - 2) by ring, neg_zsmul]
      have hxminus : xCoord W (P0 - WeierstrassCurve.Affine.Point.some u v hQns) = some s := by
        rw [hminus, xCoord_neg, hR]
        rfl
      have hslopeVal : W.addX x u (W.slope x u y (W.negY u v)) = s := by
        have := hrec.2.1
        rw [hxminus] at this
        exact (Option.some.inj this).symm
      rw [← hplus, hrec.1]
      rw [hrec.2.2, hslopeVal, hs, hwQ, hu]
      rw [show 2 * y + W.a₁ * x + W.a₃ = W.evalDivisionPolynomial x y 2 by
        rw [WeierstrassCurve.evalDivisionPolynomial_two]]
      rw [hphi_nm1', phi_eval W h (n - 2), phi_eval W h n]
      congr 1
      field_simp [hψ_n, hψ_nm1, hψ_nm2]
      have heven := evalDivisionPolynomial_even W h (n - 1)
      have heven' : W.evalDivisionPolynomial x y (-2 + n * 2) * W.evalDivisionPolynomial x y 2 =
          W.evalDivisionPolynomial x y (-2 + n) ^ 2 * W.evalDivisionPolynomial x y (-1 + n) *
              W.evalDivisionPolynomial x y (1 + n) -
            W.evalDivisionPolynomial x y (-3 + n) * W.evalDivisionPolynomial x y (-1 + n) *
              W.evalDivisionPolynomial x y n ^ 2 := by
        simpa [show -2 + n * 2 = 2 * (n - 1) by ring, show -2 + n = n - 2 by ring,
          show -1 + n = n - 1 by ring, show 1 + n = n + 1 by ring,
          show -3 + n = n - 3 by ring, show n - 1 - 1 = n - 2 by ring,
          show n - 1 + 2 = n + 1 by ring, show n - 1 - 2 = n - 3 by ring,
          show n - 1 + 1 = n by ring] using heven
      linear_combination (norm := ring)
        (1 - (W.evalDivisionPolynomial x y n) ^ 2 *
          (W.evalDivisionPolynomial x y (-2 + n)) ^ 2) * heven'
      linear_combination (norm := ring) (-1 : K) * heven'


end Generic

/-! ## 2. The precise first missing lemma -/

/-- **Exact first missing lemma (elliptic-net bridge).**

The sequence `n ↦ ψₙ(x, y)` evaluated at a fixed nonsingular affine point is
an elliptic net in the sense of Mathlib's `IsEllipticNet`:
`ER(p,q,r,s) = 0` for all `p q r s : ℤ`.

Mathlib 4.32.2 defines `normEDS` and proves its even/odd recurrences, but the
statement `IsEllipticNet (normEDS b c d)` is a TODO in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.  This is the
missing bridge from the polynomial recurrences to the point-level sequence;
it is not assumed anywhere in this file. -/
def S1372EllipticNetAtPoint (x y : K) : Prop :=
  IsEllipticNet (fun n : ℤ => W.evalDivisionPolynomial x y n)

/-- The elliptic-net property specialises to Mathlib's elliptic-sequence
predicate (the `s = 0` case of the elliptic relation). -/
theorem ellipticSequenceAtPoint_of_net {x y : K}
    (h : S1372EllipticNetAtPoint W x y) :
    IsEllipticSequence (fun n : ℤ => W.evalDivisionPolynomial x y n) :=
  IsEllipticNet.isEllipticSequence h

/-- **Exact second missing lemma (point-level `ω` identity).**

For every `n`, away from the zeros of `ψₙ`, the `2`-division-polynomial
value of the point `n • P` is `ψ_{2n}(P) / ψₙ(P) ^ 4`:

  `2 y(nP) + a₁ x(nP) + a₃ = ψ_{2n}(P) / ψₙ(P) ^ 4`.

This is the point-level form of the standard y-coordinate formula
`y(nP) = ωₙ(P) / ψₙ(P)^3`; Mathlib does not define the bivariate `ωₙ`
(explicit TODO in `DivisionPolynomial/Basic.lean`).  It is precisely the
input needed for the addition-law induction, and it is not assumed here. -/
def S1372OmegaFormula (n : ℤ) : Prop :=
  ∀ (x y : K) (h : W.Nonsingular x y),
    W.evalDivisionPolynomial x y n ≠ 0 →
      wCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
        W.evalDivisionPolynomial x y (2 * n) /
          (W.evalDivisionPolynomial x y n) ^ 4

/-! ## 3. Axiom footprint -/

#print axioms xCoordinateFormula_one
#print axioms xCoordinateFormula_two
#print axioms xCoordinateFormula_neg_iff
#print axioms detection_two_of_xCoordinateFormula_two
#print axioms xCoordinateFormula_step
#print axioms xCoord_neg
#print axioms ellipticSequenceAtPoint_of_net

end LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual