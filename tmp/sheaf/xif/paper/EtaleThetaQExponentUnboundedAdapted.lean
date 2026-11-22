import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaQExponentUnboundedAdapted

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

theorem thetaQExponent_nat_ge (N : Nat) :
    ((N : Rat) + 1) <= thetaQExponent (N + 1 : Int) := by
  unfold thetaQExponent
  have hN : (0 : Rat) <= (N : Rat) := by positivity
  nlinarith

theorem thetaQExponent_unbounded (e : HalfInt) :
    exists N : Nat, e < thetaQExponent (N + 1 : Int) := by
  obtain ⟨N, hN⟩ := exists_nat_gt e
  refine ⟨N, ?_⟩
  have hle := thetaQExponent_nat_ge N
  have hN' : e < (N : Rat) := hN
  linarith

#check thetaQExponent_unbounded

end LeanFormal.IUT.XiFPaper.EtaleThetaQExponentUnboundedAdapted
