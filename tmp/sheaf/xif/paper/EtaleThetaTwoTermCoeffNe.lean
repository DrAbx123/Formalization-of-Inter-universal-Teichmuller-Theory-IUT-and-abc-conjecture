import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTwoTermCoeffNe

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

noncomputable def thetaTermPair (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
      (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n)) +
    HahnSeries.single (thetaQExponent (-n - 1))
      (HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)))

theorem thetaQExponent_pair (n : Int) :
    thetaQExponent (-n - 1) = thetaQExponent n := by
  unfold thetaQExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

theorem thetaTermPair_coeff_ne (K : Type u) [Field K] (n : Int) (e : HalfInt)
    (h : thetaQExponent n ≠ e) :
    (thetaTermPair K n).coeff e = 0 := by
  unfold thetaTermPair
  rw [thetaQExponent_pair]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, h]

#check thetaTermPair_coeff_ne

end LeanFormal.IUT.XiFPaper.EtaleThetaTwoTermCoeffNe
