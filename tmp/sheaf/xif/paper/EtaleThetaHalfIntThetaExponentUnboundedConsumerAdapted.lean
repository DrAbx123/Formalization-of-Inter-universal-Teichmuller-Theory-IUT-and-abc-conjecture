import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentUnboundedConsumerAdapted

theorem thetaQExponent_nat_ge (N : Nat) :
    ((N : Rat) + 1) <=
      LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent (N + 1 : Int) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent
  have hN : (0 : Rat) <= (N : Rat) := by positivity
  nlinarith

theorem thetaExponent_unbounded (e : Rat) :
    exists N : Nat,
      e < LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (N + 1 : Int) := by
  obtain ⟨N, hN⟩ := exists_nat_gt e
  refine ⟨N, ?_⟩
  have hq := thetaQExponent_nat_ge N
  have hN' : e < (N : Rat) := hN
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  nlinarith

#check thetaExponent_unbounded

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentUnboundedConsumerAdapted
