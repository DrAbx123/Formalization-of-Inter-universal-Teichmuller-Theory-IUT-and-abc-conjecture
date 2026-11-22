import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

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

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
