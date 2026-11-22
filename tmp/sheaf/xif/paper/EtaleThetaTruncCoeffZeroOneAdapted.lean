import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffZeroOneAdapted

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

/-- q^0 coefficient for N=1: n=0 and n=-1 pair. -/
theorem etaleThetaTrunc_coeff_zero_one (K : Type u) [Field K] :
    (etaleThetaTrunc K 1).coeff (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  simp [etaleThetaTrunc, thetaQExponent, thetaUExponent]
  norm_num

#check etaleThetaTrunc_coeff_zero_one

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffZeroOneAdapted
