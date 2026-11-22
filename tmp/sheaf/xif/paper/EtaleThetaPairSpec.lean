import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaPairSpec

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

theorem thetaPair_spec (n : Int) :
    thetaQExponent (-n - 1) = thetaQExponent n ∧
      thetaUExponent (-n - 1) = -thetaUExponent n := by
  constructor
  · unfold thetaQExponent
    rw [show (-n - 1 : Int) = -(n + 1) by ring]
    push_cast
    ring
  · unfold thetaUExponent
    ring

#check thetaPair_spec

end LeanFormal.IUT.XiFPaper.EtaleThetaPairSpec
