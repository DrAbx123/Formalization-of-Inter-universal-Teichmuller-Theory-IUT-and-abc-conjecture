import Mathlib.NumberTheory.Padics.PadicNumbers
open LeanFormal.IUT
example : ‖((-10805 : ℤ) : ℚ_[5])‖ = (5:ℝ)⁻¹ := by norm_num
example : ‖((5:ℕ) : ℚ_[5])‖ = (5:ℝ)⁻¹ := by rw [Padic.norm_p]
