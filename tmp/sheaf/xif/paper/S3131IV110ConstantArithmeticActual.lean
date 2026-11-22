import Mathlib

/-! # S3131 IUT IV Thm 1.10 constant arithmetic (d*_mod, e*_mod) - class A -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131IV110ConstantArithmeticActual

/-- The paper constant `2^12 * 3^3 * 5` in d*_mod = 2^12*3^3*5*d_mod, e*_mod = same*e_mod. -/
def starFactor : Nat := 2 ^ 12 * 3 ^ 3 * 5

/-- e*_mod <= d*_mod whenever e_mod <= d_mod (monotonicity of the paper constants). -/
theorem estar_le_dstar (dMod eMod : Nat) (h : eMod <= dMod) :
    starFactor * eMod <= starFactor * dMod :=
  Nat.mul_le_mul_left starFactor h

/-- Concrete evaluation of the paper factor (sanity check of the extracted constant). -/
theorem starFactor_value : starFactor = 552960 := by
  unfold starFactor
  norm_num

#check estar_le_dstar
#check starFactor_value

end LeanFormal.IUT.XiFPaper.S3131IV110ConstantArithmeticActual