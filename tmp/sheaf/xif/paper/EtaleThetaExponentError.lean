import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaExponentError

abbrev HalfInt : Type := Rat

def thetaExponent (n : Int) : HalfInt := ((n : Rat) + (1 / 2 : Rat)) ^ 2 / 2

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaExponent_sub (n : Int) :
    thetaExponent n - thetaQExponent n = (1 / 8 : HalfInt) := by
  unfold thetaExponent thetaQExponent
  ring

theorem thetaExponent_abs_error (n : Int) :
    |thetaExponent n - thetaQExponent n| = (1 / 8 : HalfInt) := by
  rw [thetaExponent_sub]
  norm_num

#check thetaExponent_sub
#check thetaExponent_abs_error

end LeanFormal.IUT.XiFPaper.EtaleThetaExponentError
