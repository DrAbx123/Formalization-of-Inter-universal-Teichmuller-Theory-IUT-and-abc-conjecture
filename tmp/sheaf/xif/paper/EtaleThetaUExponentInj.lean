import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaUExponentInj

def thetaUExponent (n : Int) : Int := 2 * n + 1

theorem thetaUExponent_injective : Function.Injective thetaUExponent := by
  intro a b h
  unfold thetaUExponent at h
  omega

theorem thetaUExponent_ne_zero (n : Int) : thetaUExponent n ≠ 0 := by
  unfold thetaUExponent
  omega

theorem thetaUExponent_abs_pos (n : Int) : 0 < |thetaUExponent n| := by
  unfold thetaUExponent
  omega

#check thetaUExponent_injective
#check thetaUExponent_ne_zero
#check thetaUExponent_abs_pos

end LeanFormal.IUT.XiFPaper.EtaleThetaUExponentInj
