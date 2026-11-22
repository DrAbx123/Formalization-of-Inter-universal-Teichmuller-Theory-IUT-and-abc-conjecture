import tmp.sheaf.xif.paper.S1923NetD2
import tmp.sheaf.xif.paper.S1377OmegaFormulaActual
import tmp.sheaf.xif.paper.S1361DivisionCriterionActual

set_option maxHeartbeats 1000000

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
open LeanFormal.IUT.XiFPaper.S1361DivisionCriterionActual
open WeierstrassCurve

namespace LeanFormal.IUT.XiFPaper.S1923XCoordinateFormulaActual

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

theorem S1923EllipticNetAtPoint_of_ψ₂_ne_zero {x y : K} (h : W.Nonsingular x y)
    (h2 : W.evalDivisionPolynomial x y 2 ≠ 0) : S1372EllipticNetAtPoint W x y := by
  have eval_even : ∀ m : ℤ,
      W.evalDivisionPolynomial x y (2 * m) * W.evalDivisionPolynomial x y 2 =
        W.evalDivisionPolynomial x y (m - 1) ^ 2 * W.evalDivisionPolynomial x y m *
            W.evalDivisionPolynomial x y (m + 2) -
          W.evalDivisionPolynomial x y (m - 2) * W.evalDivisionPolynomial x y m *
            W.evalDivisionPolynomial x y (m + 1) ^ 2 := by
    intro m
    have hm := congrArg (Polynomial.evalEval x y) (W.ψ_even m)
    simpa [WeierstrassCurve.evalDivisionPolynomial] using hm
  have eval_odd : ∀ m : ℤ,
      W.evalDivisionPolynomial x y (2 * m + 1) =
        W.evalDivisionPolynomial x y (m + 2) * W.evalDivisionPolynomial x y m ^ 3 -
          W.evalDivisionPolynomial x y (m - 1) * W.evalDivisionPolynomial x y (m + 1) ^ 3 := by
    intro m
    have hm := congrArg (Polynomial.evalEval x y) (W.ψ_odd m)
    simpa [WeierstrassCurve.evalDivisionPolynomial] using hm
  have rel_even : ∀ m : ℤ,
      IsEllipticNet.rel (fun n => W.evalDivisionPolynomial x y n) (m + 1) (m - 1) 1 0 = 0 := by
    intro m
    rw [IsEllipticNet.rel_even]
    have hm := eval_even m
    simp only [WeierstrassCurve.evalDivisionPolynomial_one, one_pow, mul_one]
    linear_combination hm
  have rel_odd : ∀ m : ℤ,
      IsEllipticNet.rel (fun n => W.evalDivisionPolynomial x y n) (m + 1) m 1 0 = 0 := by
    intro m
    rw [IsEllipticNet.rel_odd]
    have hm := eval_odd m
    simp only [WeierstrassCurve.evalDivisionPolynomial_one, one_pow, mul_one]
    linear_combination hm
  exact S1923Net.IsEllipticNet.of_even_odd
    (W := fun n => W.evalDivisionPolynomial x y n)
    (neg := by intro n; simp [WeierstrassCurve.evalDivisionPolynomial_neg])
    (one := by simp)
    (two := mem_nonZeroDivisors_of_ne_zero h2)
    rel_even rel_odd

theorem S1923XCoordinateFormula_of_intermediate (n : ℤ) (hn : 1 ≤ n)
    (hψ : ∀ (x y : K) (h : W.Nonsingular x y) (k : ℤ),
      1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0) :
    s1361XCoordinateFormula W n := by
  intro x y h hne
  have h2 : W.evalDivisionPolynomial x y 2 ≠ 0 := hψ x y h 2 (by norm_num) (by omega)
  have hnet := S1923EllipticNetAtPoint_of_ψ₂_ne_zero W h h2
  exact xCoordinateFormula_of_ellipticNet W h hnet n hn (hψ x y h)

#print axioms S1923EllipticNetAtPoint_of_ψ₂_ne_zero
#print axioms S1923XCoordinateFormula_of_intermediate

end LeanFormal.IUT.XiFPaper.S1923XCoordinateFormulaActual
