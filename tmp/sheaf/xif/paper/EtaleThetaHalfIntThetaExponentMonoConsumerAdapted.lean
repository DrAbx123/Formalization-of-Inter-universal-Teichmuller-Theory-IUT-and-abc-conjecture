import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentMonoConsumerAdapted

theorem thetaExponent_nat_mono {a b : Nat} (h : a <= b) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (a + 1 : Int) <=
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (b + 1 : Int) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  have hab : (a : Rat) <= (b : Rat) := by exact_mod_cast h
  nlinarith

theorem thetaExponent_nat_strictMono {a b : Nat} (h : a < b) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (a + 1 : Int) <
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (b + 1 : Int) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  have hab : (a : Rat) < (b : Rat) := by exact_mod_cast h
  nlinarith

#check thetaExponent_nat_mono
#check thetaExponent_nat_strictMono

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentMonoConsumerAdapted
