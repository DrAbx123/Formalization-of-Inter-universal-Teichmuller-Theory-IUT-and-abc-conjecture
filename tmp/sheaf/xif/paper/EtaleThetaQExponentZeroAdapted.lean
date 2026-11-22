import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaQExponentZeroAdapted

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaQExponent_eq_zero_iff (n : Int) :
    thetaQExponent n = 0 ↔ n = 0 ∨ n = -1 := by
  constructor
  · intro h
    unfold thetaQExponent at h
    have hfac : (n : Rat) * ((n : Rat) + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with h0 | h1
    · left; exact_mod_cast h0
    · right; omega
  · rintro (rfl | rfl)
    · unfold thetaQExponent; norm_num
    · unfold thetaQExponent; norm_num

#check thetaQExponent_eq_zero_iff

end LeanFormal.IUT.XiFPaper.EtaleThetaQExponentZeroAdapted
