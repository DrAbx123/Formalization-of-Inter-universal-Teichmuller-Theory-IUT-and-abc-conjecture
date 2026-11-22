import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaThetaExponentMono

abbrev HalfInt : Type := Rat

def thetaExponent (n : Int) : HalfInt := ((n : Rat) + (1 / 2 : Rat)) ^ 2 / 2

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaExponent_eq (n : Int) :
    thetaExponent n = thetaQExponent n + (1 / 8 : HalfInt) := by
  unfold thetaExponent thetaQExponent
  ring

theorem thetaExponent_strictMono {a b : Int}
    (ha : 0 <= a) (hab : a < b) :
    thetaExponent a < thetaExponent b := by
  unfold thetaExponent
  have ha' : (0 : Rat) <= (a : Rat) := by exact_mod_cast ha
  have hab' : (a : Rat) < (b : Rat) := by exact_mod_cast hab
  nlinarith

#check thetaExponent_eq
#check thetaExponent_strictMono

end LeanFormal.IUT.XiFPaper.EtaleThetaThetaExponentMono
