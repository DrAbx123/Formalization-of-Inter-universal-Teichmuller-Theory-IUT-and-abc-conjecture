/- B1 analytic h (kurt): derivative evaluation bound from coefficient bounds.
Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiCauchyCoeffEvalActual
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyDerivativeEvalActual

open Polynomial

/-- Derivative coefficients are bounded by natDegree times the coefficient bound. -/
theorem norm_derivative_coeff_le (p : ℂ[X]) (B : ℝ)
    (hB : ∀ i, ‖p.coeff i‖ ≤ B) (hB0 : 0 ≤ B) (i : ℕ) :
    ‖p.derivative.coeff i‖ ≤ (p.natDegree : ℝ) * B := by
  by_cases hi : i + 1 ≤ p.natDegree
  · have hstep : p.derivative.coeff i = (i + 1) * p.coeff (i + 1) := by
      rw [Polynomial.coeff_derivative, nsmul_eq_mul]
      push_cast
      ring
    rw [hstep, norm_mul]
    have h1 : ‖((i + 1 : ℕ) : ℂ)‖ ≤ (p.natDegree : ℝ) := by
      rw [Complex.norm_natCast]
      exact_mod_cast hi
    have h2 : ‖p.coeff (i + 1)‖ ≤ B := hB (i + 1)
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  · have hz : p.coeff (i + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_le hi)
    have hstep : p.derivative.coeff i = (i + 1) * p.coeff (i + 1) := by
      rw [Polynomial.coeff_derivative, nsmul_eq_mul]
      push_cast
      ring
    rw [hstep, hz, mul_zero, norm_zero]
    positivity

/-- Evaluation of the derivative on the closed unit disc, from coefficient bounds. -/
theorem norm_derivative_eval_le (p : ℂ[X]) (z : ℂ) (hz : ‖z‖ ≤ 1) (B : ℝ)
    (hB : ∀ i, ‖p.coeff i‖ ≤ B) (hB0 : 0 ≤ B) :
    ‖p.derivative.eval z‖ ≤ ((p.natDegree : ℝ) + 1) *
      ((p.natDegree : ℝ) * B) := by
  have hB' : ∀ i, ‖p.derivative.coeff i‖ ≤ (p.natDegree : ℝ) * B :=
    fun i => norm_derivative_coeff_le p B hB hB0 i
  have hB'0 : 0 ≤ (p.natDegree : ℝ) * B := by positivity
  have h := Mzk1G1PsiCauchyCoeffEvalActual.norm_eval_le_of_uniform_coeff_bound
    p.derivative z hz ((p.natDegree : ℝ) * B) hB' hB'0
  refine h.trans ?_
  have hdeg : p.derivative.natDegree ≤ p.natDegree :=
    (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)
  have hcast : ((p.derivative.natDegree + 1 : ℕ) : ℝ) ≤ ((p.natDegree + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hdeg
  exact mul_le_mul_of_nonneg_right hcast hB'0

#print axioms norm_derivative_coeff_le
#print axioms norm_derivative_eval_le

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyDerivativeEvalActual
end