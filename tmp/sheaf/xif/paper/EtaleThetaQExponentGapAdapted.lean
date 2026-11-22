import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaQExponentGapAdapted

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaQExponent_succ_sub (n : Int) :
    thetaQExponent (n + 1) - thetaQExponent n = ((n : Rat) + 1) := by
  unfold thetaQExponent
  ring

theorem thetaQExponent_succ_gt {n : Int} (hn : 0 <= n) :
    thetaQExponent n < thetaQExponent (n + 1) := by
  have h := thetaQExponent_succ_sub n
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  have hpos : (0 : Rat) < (n : Rat) + 1 := by positivity
  linarith

#check thetaQExponent_succ_sub
#check thetaQExponent_succ_gt

end LeanFormal.IUT.XiFPaper.EtaleThetaQExponentGapAdapted
