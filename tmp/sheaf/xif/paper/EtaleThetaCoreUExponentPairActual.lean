import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentPairActual

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

theorem thetaUExponent_ne_neg (n : Int) :
    thetaUExponent n ≠ -thetaUExponent n := by
  unfold thetaUExponent
  omega

#check thetaUExponent_neg
#check thetaUExponent_pair_sum_zero
#check thetaUExponent_pair_abs
#check thetaUExponent_ne_neg

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentPairActual
