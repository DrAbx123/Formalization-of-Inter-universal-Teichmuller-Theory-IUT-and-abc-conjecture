import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1StepXIChartMap4Actual
open Polynomial
def fermatChartMap (n : Nat) (x _ : ℚ) : ℚ := x ^ n
noncomputable def chartPolynomial {m : Nat} (t : Fin m → ℚ) : ℚ[X] :=
  ∏ i, (X - C (t i))
theorem chartPolynomial_eval (t : Fin m → ℚ) (i : Fin m) :
    (chartPolynomial t).eval (t i) = 0 := by
  unfold chartPolynomial
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])
#print axioms chartPolynomial_eval
end LeanFormal.IUT.XiFPaper.Mzk1G1StepXIChartMap4Actual
end
