import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaThetaExponentUnbounded

abbrev HalfInt : Type := Rat

def thetaExponent (n : Int) : HalfInt := ((n : Rat) + (1 / 2 : Rat)) ^ 2 / 2

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaExponent_eq (n : Int) :
    thetaExponent n = thetaQExponent n + (1 / 8 : HalfInt) := by
  unfold thetaExponent thetaQExponent
  ring

theorem thetaQExponent_nat_ge (N : Nat) :
    ((N : Rat) + 1) <= thetaQExponent (N + 1 : Int) := by
  unfold thetaQExponent
  have hN : (0 : Rat) <= (N : Rat) := by positivity
  nlinarith

theorem thetaExponent_unbounded (e : HalfInt) :
    exists N : Nat, e < thetaExponent (N + 1 : Int) := by
  obtain ⟨N, hN⟩ := exists_nat_gt e
  refine ⟨N, ?_⟩
  have hq := thetaQExponent_nat_ge N
  have hrel := thetaExponent_eq (N + 1 : Int)
  have hN' : e < (N : Rat) := hN
  rw [hrel]
  linarith

#check thetaExponent_unbounded

end LeanFormal.IUT.XiFPaper.EtaleThetaThetaExponentUnbounded
