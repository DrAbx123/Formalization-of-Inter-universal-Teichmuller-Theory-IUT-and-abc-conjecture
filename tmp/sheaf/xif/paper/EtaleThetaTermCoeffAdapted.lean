import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTermCoeffAdapted

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

noncomputable def thetaTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

theorem thetaTerm_coeff (K : Type u) [Field K] (n : Int) :
    (thetaTerm K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) := by
  simp [thetaTerm, HahnSeries.coeff_single]

theorem thetaTerm_coeff_ne (K : Type u) [Field K] (n : Int) (e : HalfInt)
    (h : thetaQExponent n ≠ e) :
    (thetaTerm K n).coeff e = 0 := by
  simp [thetaTerm, HahnSeries.coeff_single, h]

#check thetaTerm_coeff
#check thetaTerm_coeff_ne

end LeanFormal.IUT.XiFPaper.EtaleThetaTermCoeffAdapted
