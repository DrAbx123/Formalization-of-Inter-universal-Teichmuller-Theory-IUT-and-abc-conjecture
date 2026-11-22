import Mathlib
open Polynomial
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3108X2SeparableActual
theorem S3108_derivative_X2_add_one : (Polynomial.X^2 + 1 : Polynomial ℚ).derivative = (2 : Polynomial ℚ) * Polynomial.X := by
  simp [Polynomial.derivative_X_pow]
  norm_num
theorem S3108_X2_separable : (Polynomial.X^2 + 1 : Polynomial ℚ).Separable := by
  rw [show (Polynomial.X^2 + 1 : Polynomial ℚ) = Polynomial.X^2 - Polynomial.C (-1) by simp]
  exact Polynomial.separable_X_pow_sub_C (n := 2) (a := (-1 : ℚ)) (by norm_num) (by norm_num)
end LeanFormal.IUT.XiFPaper.S3108X2SeparableActual
end
