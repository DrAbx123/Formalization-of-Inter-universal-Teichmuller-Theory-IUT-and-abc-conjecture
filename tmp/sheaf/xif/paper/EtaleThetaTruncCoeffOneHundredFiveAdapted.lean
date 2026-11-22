import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffOneHundredFiveAdapted

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

theorem etaleThetaTrunc_coeff_oneHundredFive (K : Type u) [Field K] :
    (etaleThetaTrunc K 15).coeff (thetaQExponent 14) =
      HahnSeries.single (thetaUExponent 14) (1 : K) +
        HahnSeries.single (thetaUExponent (-15)) (-1 : K) := by
  simp [etaleThetaTrunc, thetaQExponent, thetaUExponent]
  norm_num

#check etaleThetaTrunc_coeff_oneHundredFive

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffOneHundredFiveAdapted
