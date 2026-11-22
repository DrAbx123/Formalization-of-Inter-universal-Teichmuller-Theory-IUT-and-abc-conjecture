import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
import Mathlib.NumberTheory.EllipticDivisibilitySequence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

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
  simp only [show n + 2 = n + 2 by rfl, show n - 2 = n - 2 by rfl,
    show 2 + (n - 1) = n + 1 by ring, show 2 - (n - 1) = 3 - n by ring,
    show n + (n - 1) = 2 * n - 1 by ring, show n - (n - 1) = 1 by ring,
    show 3 - n = -(n - 3) by ring,
    WeierstrassCurve.evalDivisionPolynomial_one,
    WeierstrassCurve.evalDivisionPolynomial_neg] at h
  linear_combination h

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
