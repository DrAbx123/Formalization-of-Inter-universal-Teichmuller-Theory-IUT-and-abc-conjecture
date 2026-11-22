import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentInvolutionActual

theorem thetaUExponent_involution (n : Int) :
    thetaUExponent (-(-n - 1) - 1) = thetaUExponent n := by
  rw [show (-(-n - 1) - 1 : Int) = n by ring]

theorem thetaUExponent_pair_sum_zero (n : Int) :
    thetaUExponent n + thetaUExponent (-n - 1) = 0 := by
  rw [thetaUExponent_neg_succ]
  ring

theorem thetaUExponent_pair_abs (n : Int) :
    |thetaUExponent (-n - 1)| = |thetaUExponent n| := by
  rw [thetaUExponent_neg_succ]
  exact abs_neg _

#check thetaUExponent_involution
#check thetaUExponent_pair_sum_zero
#check thetaUExponent_pair_abs

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentInvolutionActual
