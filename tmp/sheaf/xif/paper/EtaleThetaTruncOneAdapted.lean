import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncOneAdapted

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

theorem etaleThetaTrunc_one (K : Type u) [Field K] :
    etaleThetaTrunc K 1 =
      HahnSeries.single (thetaQExponent 0)
          (HahnSeries.single (thetaUExponent 0) (1 : K)) +
        HahnSeries.single (thetaQExponent (-1))
          (HahnSeries.single (thetaUExponent (-1)) (-1 : K)) +
          HahnSeries.single (thetaQExponent 1)
            (HahnSeries.single (thetaUExponent 1) (-1 : K)) := by
  unfold etaleThetaTrunc
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [thetaQExponent, thetaUExponent]

#check etaleThetaTrunc_one

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncOneAdapted
