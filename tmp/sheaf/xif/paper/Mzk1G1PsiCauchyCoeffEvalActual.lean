/- B1 analytic h (kurt): evaluation bound from coefficient bounds (no splitting
hypothesis needed).  Default heartbeats.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyCoeffEvalActual

open Polynomial Finset

/-- Evaluation bound from coefficient bounds on the closed unit disc. -/
theorem norm_eval_le_of_coeff_bound (p : ℂ[X]) (α : ℂ) (hα : ‖α‖ ≤ 1)
    (B : ℕ → ℝ) (hB : ∀ i, ‖p.coeff i‖ ≤ B i) (hB0 : 0 ≤ B 0) :
    ‖p.eval α‖ ≤ (Finset.range (p.natDegree + 1)).sum B := by
  rw [Polynomial.eval_eq_sum_range]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, norm_pow]
  have hpow : ‖α‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hα
  have hcoeff : ‖p.coeff i‖ ≤ B i := hB i
  have hBnonneg : 0 ≤ B i := (norm_nonneg _).trans (hB i)
  calc ‖p.coeff i‖ * ‖α‖ ^ i ≤ B i * 1 := by
        exact mul_le_mul hcoeff hpow (by positivity) hBnonneg
    _ = B i := mul_one _

/-- Specialisation: coefficients bounded by 2^d give an evaluation bound. -/
theorem norm_eval_le_of_uniform_coeff_bound (p : ℂ[X]) (α : ℂ) (hα : ‖α‖ ≤ 1)
    (B : ℝ) (hB : ∀ i, ‖p.coeff i‖ ≤ B) (hB0 : 0 ≤ B) :
    ‖p.eval α‖ ≤ ((p.natDegree + 1 : ℕ) : ℝ) * B := by
  refine (norm_eval_le_of_coeff_bound p α hα (fun _ => B) hB hB0).trans ?_
  rw [Finset.sum_const, Finset.card_range]
  push_cast
  ring_nf
  exact le_refl _

#print axioms norm_eval_le_of_coeff_bound
#print axioms norm_eval_le_of_uniform_coeff_bound


/-- Combined bound for a monic polynomial with unit-disc roots: evaluation is at most
(natDegree+1) * 2^natDegree, assuming only a uniform coefficient bound B = 2^natDegree. -/
theorem norm_eval_le_two_pow_of_coeff_bound (p : ℂ[X]) (hp : p.Monic)
    (α : ℂ) (hα : ‖α‖ ≤ 1)
    (hB : ∀ i, ‖p.coeff i‖ ≤ (2 : ℝ) ^ p.natDegree) :
    ‖p.eval α‖ ≤ ((p.natDegree + 1 : ℕ) : ℝ) * 2 ^ p.natDegree :=
  norm_eval_le_of_uniform_coeff_bound p α hα (2 ^ p.natDegree) hB (by positivity)

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyCoeffEvalActual
end