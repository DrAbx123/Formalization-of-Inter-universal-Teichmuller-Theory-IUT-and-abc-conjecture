import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaExponentEq

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

theorem thetaQExponent_eq_iff (a b : Int) :
    thetaQExponent a = thetaQExponent b ↔ a = b ∨ a + b = -1 := by
  constructor
  · intro h
    unfold thetaQExponent at h
    have hfac : ((a : Rat) - (b : Rat)) * ((a : Rat) + (b : Rat) + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · left; omega
    · right; omega
  · rintro (rfl | h)
    · rfl
    · unfold thetaQExponent
      rw [show (b : Rat) = -(a : Rat) - 1 by omega]
      ring

theorem thetaUExponent_eq_neg_iff (a b : Int) :
    thetaUExponent a = -thetaUExponent b ↔ a + b = -1 := by
  unfold thetaUExponent
  constructor <;> intro h <;> omega

#check thetaQExponent_eq_iff
#check thetaUExponent_eq_neg_iff

end LeanFormal.IUT.XiFPaper.EtaleThetaExponentEq
