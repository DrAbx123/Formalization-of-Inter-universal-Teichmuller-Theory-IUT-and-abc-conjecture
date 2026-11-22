import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
import Mathlib.NumberTheory.EllipticDivisibilitySequence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-! ## The evaluated even/odd recurrences -/

lemma evalDivisionPolynomial_even' {x y : K} (h : W.Nonsingular x y) (m : ℤ) :
    W.evalDivisionPolynomial x y (2 * m) * W.evalDivisionPolynomial x y 2 =
      W.evalDivisionPolynomial x y (m - 1) ^ 2 * W.evalDivisionPolynomial x y m *
          W.evalDivisionPolynomial x y (m + 2) -
        W.evalDivisionPolynomial x y (m - 2) * W.evalDivisionPolynomial x y m *
          W.evalDivisionPolynomial x y (m + 1) ^ 2 := by
  have h := congrArg (Polynomial.evalEval x y) (W.ψ_even m)
  simpa [WeierstrassCurve.evalDivisionPolynomial] using h

lemma evalDivisionPolynomial_odd' {x y : K} (h : W.Nonsingular x y) (m : ℤ) :
    W.evalDivisionPolynomial x y (2 * m + 1) =
      W.evalDivisionPolynomial x y (m + 2) * W.evalDivisionPolynomial x y m ^ 3 -
        W.evalDivisionPolynomial x y (m - 1) * W.evalDivisionPolynomial x y (m + 1) ^ 3 := by
  have h := congrArg (Polynomial.evalEval x y) (W.ψ_odd m)
  simpa [WeierstrassCurve.evalDivisionPolynomial] using h

/-! ## The auxiliary addition recursion for `w` -/

theorem wCoord_add_of_X_ne {u v x y : K}
    (hA : W.Nonsingular u v) (hP : W.Nonsingular x y) (hux : u ≠ x) :
    wCoord W (WeierstrassCurve.Affine.Point.some u v hA +
        WeierstrassCurve.Affine.Point.some x y hP) =
      (wCoord W (WeierstrassCurve.Affine.Point.some x y hP) *
          (u - W.addX u x (W.slope u x v y)) -
        wCoord W (WeierstrassCurve.Affine.Point.some u v hA) *
          (x - W.addX u x (W.slope u x v y))) / (x - u) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hux, wCoord_some]
  have h := WeierstrassCurve.Affine.addY_sub_negY_addY (W := W.toAffine) v y hux
  dsimp only at h
  have hw : 2 * W.addY u x v (W.slope u x v y) + W.a₁ * W.addX u x (W.slope u x v y) + W.a₃ =
      W.addY u x v (W.slope u x v y) -
        W.negY (W.addX u x (W.slope u x v y)) (W.addY u x v (W.slope u x v y)) := by
    rw [WeierstrassCurve.Affine.negY]; ring
  rw [hw, h]
  simp only [wCoord_some, WeierstrassCurve.Affine.negY]
  ring

/-! ## The point-level `x`-difference formulae -/

lemma xDiff_succ {x y : K} (h : W.Nonsingular x y) (n : ℤ)
    (ha : W.evalDivisionPolynomial x y n ≠ 0)
    (hb : W.evalDivisionPolynomial x y (n - 1) ≠ 0) :
    (W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2 -
        (W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2 =
      - W.evalDivisionPolynomial x y (2 * n - 1) /
        ((W.evalDivisionPolynomial x y n) ^ 2 *
          (W.evalDivisionPolynomial x y (n - 1)) ^ 2) := by
  rw [phi_eval W h n, phi_eval W h (n - 1)]
  have hodd := evalDivisionPolynomial_odd' W h (n - 1)
  simp only [show n - 1 - 1 = n - 2 by ring, show n - 1 + 1 = n by ring,
    show n - 1 + 2 = n + 1 by ring, show 2 * (n - 1) + 1 = 2 * n - 1 by ring] at hodd
  field_simp [ha, hb]
  linear_combination (norm := ring) hodd

lemma xDiff_pred {x y : K} (h : W.Nonsingular x y) (n : ℤ)
    (hb : W.evalDivisionPolynomial x y (n - 1) ≠ 0) :
    (W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2 - x =
      - W.evalDivisionPolynomial x y n * W.evalDivisionPolynomial x y (n - 2) /
        (W.evalDivisionPolynomial x y (n - 1)) ^ 2 := by
  rw [phi_eval W h (n - 1)]
  simp only [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring]
  field_simp [hb]
  ring

/-! ## The algebraic `omega` step -/

lemma omega_step_algebra {a b c d e f g Bv Ev Fv : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hg : g ≠ 0)
    (hf : f * g = b ^ 2 * a * Fv - c * a * Ev ^ 2)
    (hd : d * g = c ^ 2 * b * Ev - Bv * b * a ^ 2)
    (he : e = Ev * b ^ 3 - c * a ^ 3)
    (hrel : b ^ 2 * c * Fv - a ^ 2 * Bv * Ev = g ^ 2 * e) :
    f / a ^ 4 = - (d / b ^ 4) + (g - d / b ^ 4) * (e / (a ^ 3 * c)) := by
  have hE0 : f * b ^ 4 * c + d * a ^ 4 * c - g * e * a * b ^ 4 + d * e * a = 0 := by
    have h1 : (f * b ^ 4 * c + d * a ^ 4 * c - g * e * a * b ^ 4 + d * e * a) * g = 0 := by
      linear_combination (norm := ring) (b ^ 4 * c) * hf + (a ^ 4 * c + e * a) * hd +
        (a * b ^ 4) * hrel - (a * b * (Bv * a ^ 2 - Ev * c ^ 2)) * he
    exact (mul_eq_zero.mp h1).resolve_right hg
  field_simp [ha, hb, hc, hg]
  linear_combination hE0

lemma w_recursion_algebra {a b c d e g x u X : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hxu : x - u = a * c / b ^ 2)
    (hXu : X - u = - e / (a ^ 2 * b ^ 2)) :
    (g * (u - X) - (d / b ^ 4) * (x - X)) / (x - u) =
      - (d / b ^ 4) + (g - d / b ^ 4) * (e / (a ^ 3 * c)) := by
  have h1 : u - X = e / (a ^ 2 * b ^ 2) := by linear_combination -hXu
  have hxX : x - X = a * c / b ^ 2 + e / (a ^ 2 * b ^ 2) := by
    linear_combination hxu + h1
  rw [hxX, h1, hxu]
  field_simp [ha, hb, hc]
  ring

/-! ## The `n = 2` case of the `omega` formula -/

lemma prePsi_four_eval {x y : K} (h : W.Nonsingular x y) :
    (W.preΨ 4).eval x =
      (W.a₁ * (2 * y + W.a₁ * x + W.a₃) + 2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)) *
          (W.preΨ 3).eval x - (2 * y + W.a₁ * x + W.a₃) ^ 4 := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (WeierstrassCurve.Affine.equation_iff' (W := W) x y).mp h.1
  rw [show W.preΨ 4 = W.preΨ₄ from by
        rw [show (4:ℤ) = ((4:ℕ):ℤ) by norm_num, WeierstrassCurve.preΨ_ofNat,
          WeierstrassCurve.preΨ'_four],
      show W.preΨ 3 = W.Ψ₃ from by
        rw [show (3:ℤ) = ((3:ℕ):ℤ) by norm_num, WeierstrassCurve.preΨ_ofNat,
          WeierstrassCurve.preΨ'_three]]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  linear_combination (norm := ring)
    (8 * (W.a₁ ^ 2 * x ^ 2 + 2 * W.a₁ * W.a₃ * x + 2 * W.a₁ * x * y + 2 * W.a₂ * x ^ 2 +
      W.a₃ ^ 2 + 2 * W.a₃ * y + 2 * W.a₄ * x + 2 * W.a₆ + 2 * x ^ 3 + 2 * y ^ 2)) * hE

lemma prePsi_four_eval' {x y Bv A : K} (h : W.Nonsingular x y)
    (hB : Bv = 2 * y + W.a₁ * x + W.a₃)
    (hA : A = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) :
    (W.preΨ 4).eval x = (W.a₁ * Bv + 2 * A) * (W.preΨ 3).eval x - Bv ^ 4 := by
  rw [hB, hA]
  exact prePsi_four_eval W h

lemma omega_two_final {Bv A P3 P4 : K}
    (hB : Bv ≠ 0)
    (hpre : P4 = (W.a₁ * Bv + 2 * A) * P3 - Bv ^ 4) :
    -Bv + (W.a₁ * Bv + 2 * A) * P3 / Bv ^ 3 = (P4 * Bv) / Bv ^ 4 := by
  rw [hpre]
  field_simp [hB]
  ring

theorem omegaFormula_two {x y : K} (h : W.Nonsingular x y)
    (h2 : W.evalDivisionPolynomial x y 2 ≠ 0) :
    wCoord W ((2 : ℤ) • WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y 4 /
        (W.evalDivisionPolynomial x y 2) ^ 4 := by
  set Bv : K := 2 * y + W.a₁ * x + W.a₃ with hBdef
  set A : K := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hAdef
  have hB : Bv ≠ 0 := by
    simpa [hBdef, WeierstrassCurve.evalDivisionPolynomial_two] using h2
  have hy : y ≠ W.negY x y := by
    intro hy
    exact h2 ((WeierstrassCurve.evalDivisionPolynomial_two_eq_zero_iff_negY (W := W)).mpr hy)
  have hslope : W.slope x x y y = A / Bv := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    rw [WeierstrassCurve.Affine.negY]
    simp only [hAdef, hBdef]
    congr 1
    ring
  have hX : W.addX x x (W.slope x x y y) = (W.Φ 2).eval x / Bv ^ 2 := by
    have hx2 := xCoordinateFormula_two W x y h h2
    rw [two_zsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
      WeierstrassCurve.evalDivisionPolynomial_two] at hx2
    simp only [xCoord_some] at hx2
    exact Option.some.inj hx2
  have hphi2 : (W.Φ 2).eval x = x * Bv ^ 2 - W.evalDivisionPolynomial x y 3 := by
    have hp := phi_eval W h 2
    simpa [hBdef, WeierstrassCurve.evalDivisionPolynomial_two,
      WeierstrassCurve.evalDivisionPolynomial_one] using hp
  have hXsub : W.addX x x (W.slope x x y y) - x =
      - W.evalDivisionPolynomial x y 3 / Bv ^ 2 := by
    rw [hX, hphi2]
    field_simp [hB]
    ring
  have hw : wCoord W (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h) =
      -Bv - (W.a₁ + 2 * (A / Bv)) * (W.addX x x (W.slope x x y y) - x) := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
    simp only [wCoord_some, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, hslope]
    simp only [hBdef, hAdef]
    ring
  have hw2 : wCoord W ((2 : ℤ) • WeierstrassCurve.Affine.Point.some x y h) =
      -Bv + (W.a₁ * Bv + 2 * A) * W.evalDivisionPolynomial x y 3 / Bv ^ 3 := by
    rw [two_zsmul, hw, hXsub]
    field_simp [hB]
    ring
  have hW3 : W.evalDivisionPolynomial x y 3 = (W.preΨ 3).eval x :=
    WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd (W := W) h.1
      (show ¬ Even (3:ℤ) by decide)
  have hW4 : W.evalDivisionPolynomial x y 4 = (W.preΨ 4).eval x * Bv := by
    rw [WeierstrassCurve.evalDivisionPolynomial_eq_evalEval_Ψ (W := W) h.1 4,
      WeierstrassCurve.Ψ_eq_C_preΨ_mul_ψ₂_of_even (W := W) (show Even (4:ℤ) by decide)]
    simp only [Polynomial.evalEval_mul, Polynomial.evalEval_C]
    rw [show Polynomial.evalEval x y (WeierstrassCurve.ψ₂ W) = Bv from by
      rw [hBdef, WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY]]
  rw [hw2, hW3, hW4]
  rw [show W.evalDivisionPolynomial x y 2 = Bv from by
    rw [hBdef, WeierstrassCurve.evalDivisionPolynomial_two]]
  exact omega_two_final W hB (prePsi_four_eval' W h hBdef hAdef)

/-! ## `IsEllipticNet` implies the elliptic-sequence relation -/

theorem rel3_of_ellipticNet {x y : K} (h : S1372EllipticNetAtPoint W x y) (m n r : ℤ) :
    W.evalDivisionPolynomial x y (m + n) * W.evalDivisionPolynomial x y (m - n) *
        W.evalDivisionPolynomial x y r ^ 2 =
      W.evalDivisionPolynomial x y (m + r) * W.evalDivisionPolynomial x y (m - r) *
          W.evalDivisionPolynomial x y n ^ 2 -
        W.evalDivisionPolynomial x y (n + r) * W.evalDivisionPolynomial x y (n - r) *
          W.evalDivisionPolynomial x y m ^ 2 := by
  have h0 := h m n r 0
  simp only [IsEllipticNet.rel, add_zero, sub_zero, mul_zero, pow_two] at h0 ⊢
  linear_combination h0

lemma rel3_special {x y : K} (hnet : S1372EllipticNetAtPoint W x y) (n : ℤ) :
    W.evalDivisionPolynomial x y (n + 2) * W.evalDivisionPolynomial x y (n - 2) *
        W.evalDivisionPolynomial x y (n - 1) ^ 2 =
      W.evalDivisionPolynomial x y (2 * n - 1) * W.evalDivisionPolynomial x y 2 ^ 2 +
        W.evalDivisionPolynomial x y (n + 1) * W.evalDivisionPolynomial x y (n - 3) *
          W.evalDivisionPolynomial x y n ^ 2 := by
  have h := rel3_of_ellipticNet W hnet n 2 (n - 1)
  simp only [show 2 + (n - 1) = n + 1 by ring, show 2 - (n - 1) = 3 - n by ring,
    show n + (n - 1) = 2 * n - 1 by ring, show n - (n - 1) = 1 by ring,
    show 3 - n = -(n - 3) by ring,
    WeierstrassCurve.evalDivisionPolynomial_one,
    WeierstrassCurve.evalDivisionPolynomial_neg] at h
  linear_combination h

/-! ## The simultaneous induction for the x-coordinate and the omega formula -/

/-- Simultaneous induction.  Assume the point-level division-polynomial
sequence is an elliptic net (S1372EllipticNetAtPoint).  Then, as long as
psi_1(P), ..., psi_{n+1}(P) are all nonzero, the x-coordinate formula
and the omega formula hold at n. -/
theorem xCoordinate_and_omega_of_ellipticNet {x y : K} (h : W.Nonsingular x y)
    (hnet : S1372EllipticNetAtPoint W x y)
    (n : ℤ) (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0) :
    xCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2) ∧
    wCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y (2 * n) /
        (W.evalDivisionPolynomial x y n) ^ 4 := by
  let P0 : W.Point := WeierstrassCurve.Affine.Point.some x y h
  have hmain : ∀ N : ℕ, 1 ≤ N →
      (∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) + 1 → W.evalDivisionPolynomial x y k ≠ 0) →
      xCoord W ((N : ℤ) • P0) =
        some ((W.Φ (N : ℤ)).eval x / (W.evalDivisionPolynomial x y (N : ℤ)) ^ 2) ∧
      wCoord W ((N : ℤ) • P0) =
        W.evalDivisionPolynomial x y (2 * (N : ℤ)) /
          (W.evalDivisionPolynomial x y (N : ℤ)) ^ 4 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro hN hψN
      rcases N with _ | _ | _ | M
      · omega
      · constructor
        · rw [show ((0 + 1 : ℕ) : ℤ) = 1 by norm_num, one_zsmul]
          simp [P0, xCoord, WeierstrassCurve.Φ_one, WeierstrassCurve.evalDivisionPolynomial_one]
        · rw [show ((0 + 1 : ℕ) : ℤ) = 1 by norm_num, one_zsmul]
          simp [P0, wCoord, WeierstrassCurve.evalDivisionPolynomial_two,
            WeierstrassCurve.evalDivisionPolynomial_one]
      · have h2 : W.evalDivisionPolynomial x y 2 ≠ 0 := hψN 2 (by norm_num) (by norm_num)
        constructor
        · simpa using xCoordinateFormula_two W x y h h2
        · simpa using omegaFormula_two W h h2
      · let n : ℤ := ((M + 3 : ℕ) : ℤ)
        have hn3 : 3 ≤ n := by dsimp [n]; omega
        have hn1 : 1 ≤ n := by omega
        have hψn : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0 := hψN
        have hψM2 : ∀ k : ℤ, 1 ≤ k → k ≤ ((M + 2 : ℕ) : ℤ) + 1 →
            W.evalDivisionPolynomial x y k ≠ 0 := by
          intro k hk1 hk2
          exact hψN k hk1 (by dsimp [n]; push_cast at hk2 ⊢; omega)
        have hψM1 : ∀ k : ℤ, 1 ≤ k → k ≤ ((M + 1 : ℕ) : ℤ) + 1 →
            W.evalDivisionPolynomial x y k ≠ 0 := by
          intro k hk1 hk2
          exact hψN k hk1 (by dsimp [n]; push_cast at hk2 ⊢; omega)
        have hIH2 := ih (M + 2) (by omega) (by omega) hψM2
        have hIH1 := ih (M + 1) (by omega) (by omega) hψM1
        have hxm1 : xCoord W ((n - 1) • P0) =
            some ((W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2) := by
          rw [show n - 1 = ((M + 2 : ℕ) : ℤ) by dsimp [n]; push_cast; ring]
          exact hIH2.1
        have hωm1 : wCoord W ((n - 1) • P0) =
            W.evalDivisionPolynomial x y (2 * (n - 1)) /
              (W.evalDivisionPolynomial x y (n - 1)) ^ 4 := by
          rw [show n - 1 = ((M + 2 : ℕ) : ℤ) by dsimp [n]; push_cast; ring]
          exact hIH2.2
        have hxm2 : xCoord W ((n - 2) • P0) =
            some ((W.Φ (n - 2)).eval x / (W.evalDivisionPolynomial x y (n - 2)) ^ 2) := by
          rw [show n - 2 = ((M + 1 : ℕ) : ℤ) by dsimp [n]; push_cast; ring]
          exact hIH1.1
        have hstep := xCoordinateFormula_step W n hn3 x y h hψn hxm1 hxm2 hωm1
        have hWn : W.evalDivisionPolynomial x y n ≠ 0 := hψn n (by omega) (by omega)
        have hWm : W.evalDivisionPolynomial x y (n - 1) ≠ 0 :=
          hψn (n - 1) (by omega) (by omega)
        have hWm2 : W.evalDivisionPolynomial x y (n - 2) ≠ 0 :=
          hψn (n - 2) (by omega) (by omega)
        have hW2 : W.evalDivisionPolynomial x y 2 ≠ 0 := hψn 2 (by omega) (by omega)
        rcases hnP : n • P0 with _ | ⟨X, Y, hB⟩
        · rw [hnP] at hstep
          simp [xCoord] at hstep
        · rw [hnP] at hstep
          have hX : X = (W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2 := by
            simpa [xCoord] using hstep
          rcases hmP : (n - 1) • P0 with _ | ⟨u, v, hA⟩
          · rw [hmP] at hxm1
            simp [xCoord] at hxm1
          · rw [hmP] at hxm1 hωm1
            have hu : u = (W.Φ (n - 1)).eval x /
                (W.evalDivisionPolynomial x y (n - 1)) ^ 2 := by
              simpa [xCoord] using hxm1
            have hwA : 2 * v + W.a₁ * u + W.a₃ =
                W.evalDivisionPolynomial x y (2 * (n - 1)) /
                  (W.evalDivisionPolynomial x y (n - 1)) ^ 4 := by
              simpa [wCoord] using hωm1
            set a : K := W.evalDivisionPolynomial x y n with ha_def
            set b : K := W.evalDivisionPolynomial x y (n - 1) with hb_def
            set c : K := W.evalDivisionPolynomial x y (n - 2) with hc_def
            set g : K := W.evalDivisionPolynomial x y 2 with hg_def
            set d : K := W.evalDivisionPolynomial x y (2 * n - 2) with hd_def
            set e : K := W.evalDivisionPolynomial x y (2 * n - 1) with he_def
            set f : K := W.evalDivisionPolynomial x y (2 * n) with hf_def
            set Bv : K := W.evalDivisionPolynomial x y (n - 3) with hBv_def
            set Ev : K := W.evalDivisionPolynomial x y (n + 1) with hEv_def
            set Fv : K := W.evalDivisionPolynomial x y (n + 2) with hFv_def
            have ha : a ≠ 0 := by rw [ha_def]; exact hWn
            have hb : b ≠ 0 := by rw [hb_def]; exact hWm
            have hc : c ≠ 0 := by rw [hc_def]; exact hWm2
            have hg : g ≠ 0 := by rw [hg_def]; exact hW2
            have hu_eq : u = (W.Φ (n - 1)).eval x / b ^ 2 := by
              rw [hu, hb_def]
            have hX_eq : X = (W.Φ n).eval x / a ^ 2 := by
              rw [hX, ha_def]
            have hwA_eq : 2 * v + W.a₁ * u + W.a₃ = d / b ^ 4 := by
              rw [hwA, hd_def, hb_def]
              congr 1
              ring
            have hphi_m := phi_eval W h (n - 1)
            have hphi_m' : (W.Φ (n - 1)).eval x = x * b ^ 2 - a * c := by
              rw [hb_def, hc_def, ha_def]
              simpa [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] using hphi_m
            have hphi_n := phi_eval W h n
            have hphi_n' : (W.Φ n).eval x = x * a ^ 2 - Ev * b := by
              rw [ha_def, hb_def, hEv_def]
              simpa using hphi_n
            have hxu : x - u = a * c / b ^ 2 := by
              rw [hu_eq, hphi_m']
              field_simp [hb]
              ring
            have he_odd : e = Ev * b ^ 3 - c * a ^ 3 := by
              rw [he_def, hEv_def, hb_def, hc_def, ha_def]
              have hodd := evalDivisionPolynomial_odd' W h (n - 1)
              simpa [show 2 * (n - 1) + 1 = 2 * n - 1 by ring,
                show n - 1 + 2 = n + 1 by ring, show n - 1 - 1 = n - 2 by ring,
                show n - 1 + 1 = n by ring] using hodd
            have hXu : X - u = - e / (a ^ 2 * b ^ 2) := by
              rw [hX_eq, hu_eq, hphi_n', hphi_m', he_odd]
              field_simp [ha, hb]
              ring
            have hux : u ≠ x := by
              intro hux
              have h0 : x - u = 0 := by rw [hux]; ring
              rw [hxu] at h0
              exact (div_ne_zero (mul_ne_zero ha hc) (pow_ne_zero 2 hb)) h0
            sorry
  have hN : 1 ≤ n.natAbs := by
    have h0 : (0 : ℤ) ≤ n := by omega
    have h1 := Int.natAbs_of_nonneg h0
    omega
  have h := hmain n.natAbs hN (by
    intro k hk1 hk2
    rw [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at hk2
    exact hψ k hk1 hk2)
  rwa [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at h

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual