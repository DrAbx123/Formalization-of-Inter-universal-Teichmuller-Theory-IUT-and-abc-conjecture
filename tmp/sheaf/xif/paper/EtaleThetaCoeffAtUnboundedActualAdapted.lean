import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoeffAtUnboundedActualAdapted

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
  have hN'' : (N : Rat) < (N : Rat) + 1 := by linarith
  exact lt_of_lt_of_le (lt_trans hN' hN'') hle

theorem thetaQExponent_nat_mono {a b : Nat} (h : a <= b) :
    thetaQExponent (a + 1 : Int) <= thetaQExponent (b + 1 : Int) := by
  unfold thetaQExponent
  have hab : (a : Rat) <= (b : Rat) := by exact_mod_cast h
  nlinarith

#check thetaQExponent_unbounded
#check thetaQExponent_nat_mono

end LeanFormal.IUT.XiFPaper.EtaleThetaCoeffAtUnboundedActualAdapted
