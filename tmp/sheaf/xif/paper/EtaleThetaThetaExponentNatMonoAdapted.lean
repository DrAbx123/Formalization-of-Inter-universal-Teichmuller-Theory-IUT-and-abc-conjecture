import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaThetaExponentNatMonoAdapted

abbrev HalfInt : Type := Rat

def thetaExponent (n : Int) : HalfInt := ((n : Rat) + (1 / 2 : Rat)) ^ 2 / 2

theorem thetaExponent_nat_mono {a b : Nat} (h : a <= b) :
    thetaExponent (a + 1 : Int) <= thetaExponent (b + 1 : Int) := by
  unfold thetaExponent
  have hab : (a : Rat) <= (b : Rat) := by exact_mod_cast h
  nlinarith

#check thetaExponent_nat_mono

end LeanFormal.IUT.XiFPaper.EtaleThetaThetaExponentNatMonoAdapted
