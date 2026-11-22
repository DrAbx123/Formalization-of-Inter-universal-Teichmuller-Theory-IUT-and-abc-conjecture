import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

theorem thetaQExponent_neg_succ (n : Int) :
    thetaQExponent (-n - 1) = thetaQExponent n := by
  unfold thetaQExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

theorem thetaUExponent_neg_succ (n : Int) :
    thetaUExponent (-n - 1) = -thetaUExponent n := by
  unfold thetaUExponent
  ring

theorem thetaUExponent_odd (n : Int) :
    exists m : Int, thetaUExponent n = 2 * m + 1 := by
  exact ⟨n, rfl⟩

theorem thetaQExponent_zero : thetaQExponent 0 = 0 := by
  unfold thetaQExponent
  norm_num

theorem thetaUExponent_zero : thetaUExponent 0 = 1 := by
  unfold thetaUExponent
  norm_num

#check thetaQExponent_neg_succ
#check thetaUExponent_neg_succ
#check thetaUExponent_odd
#check thetaQExponent_zero
#check thetaUExponent_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing
