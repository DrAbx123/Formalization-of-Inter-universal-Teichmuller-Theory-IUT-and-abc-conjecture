import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic

noncomputable section
namespace Probe5
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

#check Padic.norm_natCast_eq_one_iff (p := 5) (n := 61)
#check Padic.norm_natCast_eq_one_iff

example : ‖((61:ℕ) : ℚ_[5])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  norm_num

example : ‖((61:ℕ) : ℚ_[5])‖ = 1 := by
  exact (Padic.norm_natCast_eq_one_iff (p := 5) (n := 61)).2 (by norm_num)

example : ‖(61/64 : ℚ_[5])‖ = 1 := by
  rw [show (61/64 : ℚ_[5]) = ((61:ℕ):ℚ_[5]) / ((64:ℕ):ℚ_[5]) by norm_num]
  rw [norm_div]
  have h1 : ‖((61:ℕ) : ℚ_[5])‖ = 1 := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 61)).2 (by norm_num)
  have h2 : ‖((64:ℕ) : ℚ_[5])‖ = 1 := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 64)).2 (by norm_num)
  rw [h1, h2]
  norm_num

end Probe5
