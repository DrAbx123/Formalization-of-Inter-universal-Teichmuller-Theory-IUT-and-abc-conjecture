import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncationStableOfLt

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def etaleThetaTruncOneSided (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaTermEx K (k : Int))

theorem etaleThetaTruncOneSided_succ (K : Type u) [Field K] (N : Nat) :
    etaleThetaTruncOneSided K (N + 1) =
      etaleThetaTruncOneSided K N + thetaTermEx K (N + 1 : Int) := by
  simp [etaleThetaTruncOneSided, Finset.sum_range_succ]

theorem etaleThetaTruncOneSided_coeff_stable_of_lt (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) (h : e < thetaQExponent (N + 1 : Int)) :
    (etaleThetaTruncOneSided K (N + 1)).coeff e =
      (etaleThetaTruncOneSided K N).coeff e := by
  rw [etaleThetaTruncOneSided_succ, HahnSeries.coeff_add]
  have hne : e ≠ thetaQExponent (N + 1 : Int) := ne_of_lt h
  have hz : (thetaTermEx K (N + 1 : Int)).coeff e = 0 := by
    simp [thetaTermEx, HahnSeries.coeff_single, hne]
  rw [hz, add_zero]

#check etaleThetaTruncOneSided_coeff_stable_of_lt

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncationStableOfLt
