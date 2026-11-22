import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt

/-- Half-integer exponents, represented inside Q. -/
abbrev HalfInt : Type := Rat

def halfInt (n : Int) : HalfInt := (n : Rat) / 2

/-- (1/2) * (n + 1/2)^2, the [EtTh] theta exponent before extracting q^{-1/8}. -/
def thetaExponent (n : Int) : HalfInt :=
  ((n : Rat) + (1 / 2 : Rat)) ^ 2 / 2

/-- n(n+1)/2, the [EtTh] theta q-exponent after extracting q^{-1/8}. -/
def thetaQExponent (n : Int) : HalfInt :=
  (n : Rat) * ((n : Rat) + 1) / 2

/-- 2n+1, the [EtTh] theta U-exponent. -/
def thetaUExponent (n : Int) : Int := 2 * n + 1

theorem thetaExponent_eq (n : Int) :
    thetaExponent n = thetaQExponent n + (1 / 8 : HalfInt) := by
  unfold thetaExponent thetaQExponent
  ring

#check HalfInt
#check halfInt
#check thetaExponent
#check thetaQExponent
#check thetaUExponent
#check thetaExponent_eq
#check HahnSeries HalfInt

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt
