import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncOneSidedCoeffZero

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

theorem thetaQExponent_pos_of_nat (N : Nat) :
    thetaQExponent (N + 1 : Int) ≠ 0 := by
  unfold thetaQExponent
  have h : (0 : Rat) < ((N + 1 : Nat) : Rat) := by positivity
  have h' : (0 : Rat) < ((N + 1 : Nat) : Rat) + 1 := by positivity
  positivity

theorem etaleThetaTruncOneSided_coeff_zero (K : Type u) [Field K] (N : Nat) :
    (etaleThetaTruncOneSided K N).coeff (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) := by
  induction N with
  | zero => simp [etaleThetaTruncOneSided, thetaQExponent, thetaUExponent]
  | succ N ih =>
      rw [etaleThetaTruncOneSided_succ, HahnSeries.coeff_add, ih]
      have hz : (thetaTermEx K (N + 1 : Int)).coeff (0 : HalfInt) = 0 := by
        simp [thetaTermEx, HahnSeries.coeff_single, thetaQExponent_pos_of_nat N]
      rw [hz, add_zero]

#check etaleThetaTruncOneSided_coeff_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncOneSidedCoeffZero
