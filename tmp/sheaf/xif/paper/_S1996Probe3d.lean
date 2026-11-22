import Mathlib.NumberTheory.Padics.PadicNumbers
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
example : ‖(5 : ℚ_[5])‖ = (5 : ℝ)⁻¹ := by
  rw [Padic.norm_p]
example : ‖(5 : ℚ_[5])‖ = (5 : ℝ)⁻¹ := by
  norm_num [Padic.norm_p]
example : ‖(5 : ℚ_[5])‖ = (5 : ℝ)⁻¹ := by
  rw [show (5 : ℚ_[5]) = ((5 : ℕ) : ℚ_[5]) by norm_num]
  rw [Padic.norm_natCast]
  rw [padicValNat_self]
  norm_num
