import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic

noncomputable section
namespace Probe4
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

example : ‖(61 : ℚ_[5])‖ = 1 := by
  change ‖((61 : ℕ) : ℚ_[5])‖ = 1
  rw [Padic.norm_natCast_eq_one_iff]
  norm_num

example : ‖(61/64 : ℚ_[5])‖ = 1 := by
  norm_num
  push_cast
  rw [Padic.norm_natCast_eq_one_iff, Padic.norm_natCast_eq_one_iff]
  norm_num

example : ‖(61/64 : ℚ_[5])‖ = 1 := by
  rw [show (61/64 : ℚ_[5]) = ((61:ℕ):ℚ_[5]) / ((64:ℕ):ℚ_[5]) by norm_num]
  rw [norm_div, Padic.norm_natCast_eq_one_iff, Padic.norm_natCast_eq_one_iff]
  norm_num

example : ‖(-125/64 : ℚ_[5])‖ = 1 := by
  rw [show (-125/64 : ℚ_[5]) = ((-125:ℤ):ℚ_[5]) / ((64:ℕ):ℚ_[5]) by norm_num]
  rw [norm_div, Padic.norm_intCast_eq_one_iff, Padic.norm_natCast_eq_one_iff]
  norm_num

end Probe4
