import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1StepXIChartMap2Actual
open Polynomial
/-- The Fermat chart projection `Y_n -> P1`, `(x,y) |-> x^n`. -/
def fermatChartMap (n : Nat) (x y : ℚ) : ℚ := x ^ n
/-- Protected finite chart values. -/
def protectedValues {m : Nat} (t : Fin m → ℚ) : Set ℚ := Set.range t
/-- The polynomial `g = prod (X - t_i)`. -/
noncomputable def chartPolynomial {m : Nat} (t : Fin m → ℚ) : ℚ[X] :=
  ∏ i, (X - C (t i))
theorem chartPolynomial_eval (t : Fin m → ℚ) (i : Fin m) :
    (chartPolynomial t).eval (t i) = 0 := by
  unfold chartPolynomial
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C])
theorem chartPolynomial_derivative_eval
    {m : Nat} (t : Fin m → ℚ) (i : Fin m) :
    (chartPolynomial t).derivative.eval (t i) =
      ∏ j ∈ Finset.univ.erase i, (t i - t j) := by
  unfold chartPolynomial
  rw [Polynomial.derivative_prod_finset]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.eval_mul]
    have h : (Polynomial.derivative (X - C (t i))).eval (t i) = 1 := by
      simp
    rw [h, one_mul]
    rw [Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  · intro j _ hji
    have h : (Polynomial.derivative (X - C (t j))).eval (t i) = 1 := by simp
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    rw [h, one_mul]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]; ring)
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
end LeanFormal.IUT.XiFPaper.Mzk1G1StepXIChartMap2Actual
end