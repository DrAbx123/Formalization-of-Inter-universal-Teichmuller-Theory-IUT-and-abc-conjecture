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

example {x y : K} (h : W.Nonsingular x y) :
    W.evalDivisionPolynomial x y 4 = (W.preΨ 4).eval x * W.evalDivisionPolynomial x y 2 := by
  rw [WeierstrassCurve.evalDivisionPolynomial_eq_evalEval_Ψ (W := W) h.1 4,
    WeierstrassCurve.Ψ_eq_C_preΨ_mul_ψ₂_of_even (W := W) (show Even (4:ℤ) by decide)]
  simp [Polynomial.evalEval_mul, Polynomial.evalEval_C, WeierstrassCurve.evalDivisionPolynomial]

example {x y : K} (h : W.Nonsingular x y) :
    W.evalDivisionPolynomial x y 3 = (W.preΨ 3).eval x := by
  rw [WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd (W := W) h.1
    (show ¬ Even (3:ℤ) by decide)]

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
