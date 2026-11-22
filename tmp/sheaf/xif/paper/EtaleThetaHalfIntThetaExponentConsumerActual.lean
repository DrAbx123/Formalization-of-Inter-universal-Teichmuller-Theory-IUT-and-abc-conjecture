import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaHalfIntInjActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentConsumerActual

theorem thetaExponent_eq_thetaQExponent (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n =
      LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent n + (1 / 8 : Rat) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent
  ring

theorem thetaExponent_strictMono_nonneg {a b : Int}
    (ha : 0 <= a) (hab : a < b) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent a <
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent b := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  have ha' : (0 : Rat) <= (a : Rat) := by exact_mod_cast ha
  have hab' : (a : Rat) < (b : Rat) := by exact_mod_cast hab
  nlinarith

#check thetaExponent_eq_thetaQExponent
#check thetaExponent_strictMono_nonneg

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentConsumerActual
