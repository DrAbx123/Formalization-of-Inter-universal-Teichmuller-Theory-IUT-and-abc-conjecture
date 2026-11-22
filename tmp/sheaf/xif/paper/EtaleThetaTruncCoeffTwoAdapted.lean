import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffTwoAdapted

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

/-- q_X^2 coefficient of the truncated [EtTh] theta series vanishes:
    n(n+1)/2 = 2 has no integer solution. -/
theorem etaleThetaTrunc_coeff_two (K : Type u) [Field K] :
    (etaleThetaTrunc K 2).coeff (2 : HalfInt) = 0 := by
  simp [etaleThetaTrunc, thetaQExponent, thetaUExponent]
  norm_num

#check etaleThetaTrunc_coeff_two

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffTwoAdapted
