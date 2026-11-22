import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic

noncomputable section
namespace Probe2
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

example : ‖(61 : ℚ_[5])‖ = 1 := by simp
example : ‖(64 : ℚ_[5])‖ = 1 := by simp
example : ‖(61/64 : ℚ_[5])‖ = 1 := by
  rw [div_eq_mul_inv]
  simp
example : ‖(-125/64 : ℚ_[5])‖ = 1 := by
  rw [div_eq_mul_inv]
  simp
example : ‖(27721/256 : ℚ_[5])‖ = 1 := by
  rw [div_eq_mul_inv]
  simp
example : ‖(558140625/1048576 : ℚ_[5])‖ < 1 := by
  rw [div_eq_mul_inv]
  have h1 : ‖(558140625 : ℚ_[5])‖ = (5 : ℝ)⁻¹ := by
    rw [show (558140625 : ℚ_[5]) = (5 : ℚ_[5])^6 * (35721 : ℚ_[5]) by norm_num]
    rw [norm_mul, Padic.norm_p_pow]
    have : ‖(35721 : ℚ_[5])‖ = 1 := by simp
    rw [this, mul_one]
    norm_num
  rw [h1]
  have h2 : ‖(1048576 : ℚ_[5])‖ = 1 := by simp
  rw [norm_inv, h2]
  simp
  norm_num

end Probe2
