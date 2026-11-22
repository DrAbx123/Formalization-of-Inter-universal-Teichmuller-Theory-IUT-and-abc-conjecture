import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffFortyFiveAdapted

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

noncomputable def etaleThetaTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (2 * N + 1)) (fun k : Nat =>
    let n : Int := (k : Int) - (N : Int)
    HahnSeries.single (thetaQExponent n)
      (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n)))

theorem etaleThetaTrunc_coeff_fortyFive (K : Type u) [Field K] :
    (etaleThetaTrunc K 10).coeff (thetaQExponent 9) =
      HahnSeries.single (thetaUExponent 9) (-1 : K) +
        HahnSeries.single (thetaUExponent (-10)) (1 : K) := by
  simp [etaleThetaTrunc, thetaQExponent, thetaUExponent]
  norm_num

#check etaleThetaTrunc_coeff_fortyFive

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffFortyFiveAdapted
