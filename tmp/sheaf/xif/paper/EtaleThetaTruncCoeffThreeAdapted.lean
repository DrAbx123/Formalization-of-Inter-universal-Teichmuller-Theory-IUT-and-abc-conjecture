import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffThreeAdapted

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

/-- The first nontrivial theta coefficient: q_X^3 pairs n=2 and n=-3. -/
theorem etaleThetaTrunc_coeff_three (K : Type u) [Field K] :
    (etaleThetaTrunc K 3).coeff (thetaQExponent 2) =
      HahnSeries.single (thetaUExponent 2) (1 : K) +
        HahnSeries.single (thetaUExponent (-3)) (-1 : K) := by
  simp [etaleThetaTrunc, thetaQExponent, thetaUExponent]
  norm_num

#check etaleThetaTrunc_coeff_three

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffThreeAdapted
