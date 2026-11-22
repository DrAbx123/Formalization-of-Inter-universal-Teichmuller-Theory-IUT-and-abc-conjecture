import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic

noncomputable section
namespace Probe3
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

example : ‖(61 : ℚ_[5])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  norm_num

example : ‖(61/64 : ℚ_[5])‖ = 1 := by
  norm_num
  rw [Padic.norm_natCast_eq_one_iff, Padic.norm_natCast_eq_one_iff]
  norm_num

example : ‖(61/64 : ℚ_[5])‖ = 1 := by
  rw [show (61/64 : ℚ_[5]) = (61 : ℚ_[5]) / (64 : ℚ_[5]) by norm_num]
  rw [norm_div, Padic.norm_natCast_eq_one_iff, Padic.norm_natCast_eq_one_iff]
  norm_num

example : ‖(-125/64 : ℚ_[5])‖ = 1 := by
  rw [show (-125/64 : ℚ_[5]) = (-125 : ℚ_[5]) / (64 : ℚ_[5]) by norm_num]
  rw [norm_div]
  have h1 : ‖(-125 : ℚ_[5])‖ = 1 := by
    rw [show (-125 : ℚ_[5]) = ((-125 : ℤ) : ℚ_[5]) by norm_num]
    rw [Padic.norm_intCast_eq_one_iff]
    norm_num
  rw [h1, Padic.norm_natCast_eq_one_iff]
  norm_num

end Probe3
