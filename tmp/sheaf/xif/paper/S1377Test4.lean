import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
import Mathlib.NumberTheory.EllipticDivisibilitySequence

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

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
