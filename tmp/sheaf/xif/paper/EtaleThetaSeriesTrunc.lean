import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSeriesTrunc

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

/-- Finite symmetric truncation of the [EtTh] theta series. -/
noncomputable def etaleThetaTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (2 * N + 1)) (fun k : Nat =>
    let n : Int := (k : Int) - (N : Int)
    HahnSeries.single (thetaQExponent n)
      (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n)))

theorem etaleThetaTrunc_zero (K : Type u) [Field K] :
    etaleThetaTrunc K 0 =
      HahnSeries.single (thetaQExponent 0)
        (HahnSeries.single (thetaUExponent 0) (1 : K)) := by
  simp [etaleThetaTrunc]

#check etaleThetaTrunc
#check etaleThetaTrunc_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaSeriesTrunc
