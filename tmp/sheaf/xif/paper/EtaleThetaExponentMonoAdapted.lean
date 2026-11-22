import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaExponentMonoAdapted

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaQExponent_nonneg {n : Int} (h : 0 <= n) :
    0 <= thetaQExponent n := by
  unfold thetaQExponent
  positivity

theorem thetaQExponent_strictMono {a b : Int}
    (ha : 0 <= a) (hab : a < b) :
    thetaQExponent a < thetaQExponent b := by
  unfold thetaQExponent
  nlinarith

theorem thetaQExponent_le_of_le {a b : Int}
    (ha : 0 <= a) (hab : a <= b) :
    thetaQExponent a <= thetaQExponent b := by
  rcases lt_or_eq_of_le hab with h | h
  · exact le_of_lt (thetaQExponent_strictMono ha h)
  · rw [h]

#check thetaQExponent_nonneg
#check thetaQExponent_strictMono
#check thetaQExponent_le_of_le

end LeanFormal.IUT.XiFPaper.EtaleThetaExponentMonoAdapted
