import Mathlib
open Polynomial
noncomputable section
namespace Probe
theorem S3108_X2_separable : (Polynomial.X^2 + 1 : Polynomial ℚ).Separable := by
  rw [show (Polynomial.X^2 + 1 : Polynomial ℚ) = Polynomial.X^2 - Polynomial.C (-1) by simp]
  exact Polynomial.separable_X_pow_sub_C (n := 2) (a := (-1 : ℚ)) (by norm_num)
end Probe
end
