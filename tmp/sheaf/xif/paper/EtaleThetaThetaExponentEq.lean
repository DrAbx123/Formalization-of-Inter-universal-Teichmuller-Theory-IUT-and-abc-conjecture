import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaThetaExponentEq

abbrev HalfInt : Type := Rat

def thetaExponent (n : Int) : HalfInt := ((n : Rat) + (1 / 2 : Rat)) ^ 2 / 2

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaExponent_eq (n : Int) :
    thetaExponent n = thetaQExponent n + (1 / 8 : HalfInt) := by
  unfold thetaExponent thetaQExponent
  ring

theorem thetaExponent_neg_succ (n : Int) :
    thetaExponent (-n - 1) = thetaExponent n := by
  unfold thetaExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

#check thetaExponent_eq
#check thetaExponent_neg_succ

end LeanFormal.IUT.XiFPaper.EtaleThetaThetaExponentEq
