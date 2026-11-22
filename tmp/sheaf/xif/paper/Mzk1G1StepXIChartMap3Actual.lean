import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1StepXIChartMap3Actual
open Polynomial
/-- Fermat chart projection `(x,y) |-> x^n`. -/
def fermatChartMap (n : Nat) (x y : ℚ) : ℚ := x ^ n
noncomputable def chartPolynomial {m : Nat} (t : Fin m → ℚ) : ℚ[X] :=
  ∏ i, (X - C (t i))
theorem chartPolynomial_eval (t : Fin m → ℚ) (i : Fin m) :
    (chartPolynomial t).eval (t i) = 0 := by
  unfold chartPolynomial
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])
theorem chartPolynomial_derivative_eval
    {m : Nat} (t : Fin m → ℚ) (i : Fin m) :
    (chartPolynomial t).derivative.eval (t i) =
      ∏ j ∈ Finset.univ.erase i, (t i - t j) := by
  unfold chartPolynomial
  rw [Polynomial.derivative_prod_finset]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.eval_mul, Polynomial.eval_prod]
    rw [Polynomial.derivative_X_sub_C, Polynomial.eval_one]
    rw [mul_one]
    apply Finset.prod_congr rfl
    intro j _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  · intro j _ hji
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    have h0 : (Polynomial.eval (t i)) (X - C (t j)) = 0 := by
      simp
    have hmem : i ∈ Finset.univ.erase j := by
      exact Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩
    have hzero : (Polynomial.eval (t i)) (X - C (t i)) = 0 := by simp
    rw [Finset.prod_eq_zero hmem hzero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
theorem chart_unramified_at (t : Fin m → ℚ) (hbool : Function.Injective t)
    (i : Fin m) :
    (chartPolynomial t).derivative.eval (t i) ≠ 0 := by
  rw [chartPolynomial_derivative_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  intro hzero
  apply hji
  apply hbool
  linarith
#print axioms chartPolynomial_eval
#print axioms chart_unramified_at
end LeanFormal.IUT.XiFPaper.Mzk1G1StepXIChartMap3Actual
end