import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffZero

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

noncomputable def etaleThetaSymmetricTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaPairTerm K (k : Int))

theorem thetaQExponent_zero : thetaQExponent 0 = 0 := by
  unfold thetaQExponent
  norm_num

theorem etaleThetaSymmetricTrunc_coeff_zero (K : Type u) [Field K]
    (N : Nat) :
    (etaleThetaSymmetricTrunc K N).coeff (thetaQExponent 0) =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  induction N with
  | zero =>
      simp [etaleThetaSymmetricTrunc, thetaPairTerm, thetaTermEx, thetaQExponent, thetaUExponent]
      norm_num
  | succ N ih =>
      unfold etaleThetaSymmetricTrunc at ih ⊢
      rw [Finset.sum_range_succ, HahnSeries.coeff_add, ih]
      have hz : (thetaPairTerm K (N + 1 : Int)).coeff (thetaQExponent 0) = 0 := by
        have hne : thetaQExponent (N + 1 : Int) ≠ thetaQExponent 0 := by
          unfold thetaQExponent
          have hpos : (0 : Rat) < ((N : Rat) + 1) := by positivity
          nlinarith
        unfold thetaPairTerm
        rw [show thetaQExponent (-(N + 1 : Int) - 1) = thetaQExponent (N + 1 : Int) by
          unfold thetaQExponent
          rw [show (-(N + 1 : Int) - 1 : Int) = -((N + 1 : Int) + 1) by ring]
          push_cast
          ring]
        simp [thetaTermEx, HahnSeries.coeff_add, HahnSeries.coeff_single, hne]
      rw [hz, add_zero]

#check etaleThetaSymmetricTrunc_coeff_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffZero
