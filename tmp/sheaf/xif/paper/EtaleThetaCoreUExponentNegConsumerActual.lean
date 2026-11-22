import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentNegConsumerActual

theorem thetaUExponent_neg (n : Int) :
    thetaUExponent (-n - 1) = -thetaUExponent n := thetaUExponent_neg_succ n

theorem thetaUExponent_pair_sum_zero (n : Int) :
    thetaUExponent n + thetaUExponent (-n - 1) = 0 := by
  rw [thetaUExponent_neg]
  ring

theorem thetaUExponent_pair_abs (n : Int) :
    |thetaUExponent (-n - 1)| = |thetaUExponent n| := by
  rw [thetaUExponent_neg]
  exact abs_neg _

#check thetaUExponent_neg
#check thetaUExponent_pair_sum_zero
#check thetaUExponent_pair_abs

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentNegConsumerActual
