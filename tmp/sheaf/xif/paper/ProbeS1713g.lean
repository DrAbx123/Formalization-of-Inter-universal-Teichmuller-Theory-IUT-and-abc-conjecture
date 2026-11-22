import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic

noncomputable section
namespace Probe7
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
abbrev K5 := ℚ_[5]

example : IsCoprime (-125 : ℤ) (5 : ℤ) := by decide

example : ‖((-125:ℤ) : K5)‖ = 1 := by
  rw [Padic.norm_intCast_eq_one_iff]
  decide

example : ((64:ℕ) : ZMod 5) = 4 := by norm_num
example : ((61:ℕ) : ZMod 5) = 1 := by norm_num
example : PadicInt.toZMod (64 : ℤ_[5]) = 4 := by
  rw [show (64 : ℤ_[5]) = ((64:ℕ) : ℤ_[5]) by norm_num]
  rw [map_natCast]
  norm_num

example : PadicInt.toZMod (61 : ℤ_[5]) = 1 := by
  rw [show (61 : ℤ_[5]) = ((61:ℕ) : ℤ_[5]) by norm_num]
  rw [map_natCast]
  norm_num

end Probe7
