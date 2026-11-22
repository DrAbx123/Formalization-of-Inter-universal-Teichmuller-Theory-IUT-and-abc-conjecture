import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

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

lemma prePsi_four_eval' {x y B A : K} (h : W.Nonsingular x y)
    (hB : B = 2 * y + W.a₁ * x + W.a₃)
    (hA : A = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) :
    (W.preΨ 4).eval x = (W.a₁ * B + 2 * A) * (W.preΨ 3).eval x - B ^ 4 := by
  rw [hB, hA]
  exact prePsi_four_eval W h

lemma omega_two_final {B A P3 P4 : K}
    (hB : B ≠ 0)
    (hpre : P4 = (W.a₁ * B + 2 * A) * P3 - B ^ 4) :
    -B + (W.a₁ * B + 2 * A) * P3 / B ^ 3 = (P4 * B) / B ^ 4 := by
  rw [hpre]
  field_simp [hB]
  ring

theorem omegaFormula_two {x y : K} (h : W.Nonsingular x y)
    (h2 : W.evalDivisionPolynomial x y 2 ≠ 0) :
    wCoord W ((2 : ℤ) • WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y 4 /
        (W.evalDivisionPolynomial x y 2) ^ 4 := by
  set B : K := 2 * y + W.a₁ * x + W.a₃ with hBdef
  set A : K := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hAdef
  have hB : B ≠ 0 := by
    simpa [hBdef, WeierstrassCurve.evalDivisionPolynomial_two] using h2
  have hy : y ≠ W.negY x y := by
    intro hy
    exact h2 ((WeierstrassCurve.evalDivisionPolynomial_two_eq_zero_iff_negY (W := W)).mpr hy)
  have hslope : W.slope x x y y = A / B := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    rw [WeierstrassCurve.Affine.negY]
    simp only [hAdef, hBdef]
    congr 1
    ring
  have hX : W.addX x x (W.slope x x y y) = (W.Φ 2).eval x / B ^ 2 := by
    have hx2 := xCoordinateFormula_two W x y h h2
    rw [two_zsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
      WeierstrassCurve.evalDivisionPolynomial_two] at hx2
    simp only [xCoord_some] at hx2
    exact Option.some.inj hx2
  have hphi2 : (W.Φ 2).eval x = x * B ^ 2 - W.evalDivisionPolynomial x y 3 := by
    have hp := phi_eval W h 2
    simpa [hBdef, WeierstrassCurve.evalDivisionPolynomial_two,
      WeierstrassCurve.evalDivisionPolynomial_one] using hp
  have hXsub : W.addX x x (W.slope x x y y) - x =
      - W.evalDivisionPolynomial x y 3 / B ^ 2 := by
    rw [hX, hphi2]
    field_simp [hB]
    ring
  have hw : wCoord W (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h) =
      -B - (W.a₁ + 2 * (A / B)) * (W.addX x x (W.slope x x y y) - x) := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
    simp only [wCoord_some, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, hslope]
    simp only [hBdef, hAdef]
    ring
  have hw2 : wCoord W ((2 : ℤ) • WeierstrassCurve.Affine.Point.some x y h) =
      -B + (W.a₁ * B + 2 * A) * W.evalDivisionPolynomial x y 3 / B ^ 3 := by
    rw [two_zsmul, hw, hXsub]
    field_simp [hB]
    ring
  have hW3 : W.evalDivisionPolynomial x y 3 = (W.preΨ 3).eval x :=
    WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd (W := W) h.1
      (show ¬ Even (3:ℤ) by decide)
  have hW4 : W.evalDivisionPolynomial x y 4 = (W.preΨ 4).eval x * B := by
    rw [WeierstrassCurve.evalDivisionPolynomial_eq_evalEval_Ψ (W := W) h.1 4,
      WeierstrassCurve.Ψ_eq_C_preΨ_mul_ψ₂_of_even (W := W) (show Even (4:ℤ) by decide)]
    simp only [Polynomial.evalEval_mul, Polynomial.evalEval_C]
    rw [show Polynomial.evalEval x y (WeierstrassCurve.ψ₂ W) = B from by
      rw [hBdef, WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY]]
  rw [hw2, hW3, hW4]
  rw [show W.evalDivisionPolynomial x y 2 = B from by
    rw [hBdef, WeierstrassCurve.evalDivisionPolynomial_two]]
  exact omega_two_final W hB (prePsi_four_eval' W h hBdef hAdef)

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
