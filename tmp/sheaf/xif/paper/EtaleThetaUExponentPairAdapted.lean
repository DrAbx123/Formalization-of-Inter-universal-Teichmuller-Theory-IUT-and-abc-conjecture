import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaUExponentPairAdapted

def thetaUExponent (n : Int) : Int := 2 * n + 1

theorem thetaUExponent_pair_add_zero (n : Int) :
    thetaUExponent n + thetaUExponent (-n - 1) = 0 := by
  unfold thetaUExponent
  omega

theorem thetaUExponent_pair_abs (n : Int) :
    |thetaUExponent (-n - 1)| = |thetaUExponent n| := by
  unfold thetaUExponent
  omega

#check thetaUExponent_pair_add_zero
#check thetaUExponent_pair_abs

end LeanFormal.IUT.XiFPaper.EtaleThetaUExponentPairAdapted
