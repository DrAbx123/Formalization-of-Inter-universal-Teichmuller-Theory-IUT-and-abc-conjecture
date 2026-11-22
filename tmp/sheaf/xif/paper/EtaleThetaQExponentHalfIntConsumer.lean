import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaQExponentHalfIntConsumer

theorem thetaQExponent_eq_halfInt (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent n =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
  push_cast
  ring

theorem thetaQExponent_nat_eq_halfInt (n : Nat) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent (n : Int) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (((n * (n + 1) : Nat) : Int)) :=
  thetaQExponent_eq_halfInt (n : Int)

#check thetaQExponent_eq_halfInt
#check thetaQExponent_nat_eq_halfInt

end LeanFormal.IUT.XiFPaper.EtaleThetaQExponentHalfIntConsumer
