import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffOneAllAdapted

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

theorem thetaQExponent_ne_one_of_ge_two {n : Int} (h : 2 <= n) :
    thetaQExponent n ≠ 1 := by
  unfold thetaQExponent
  intro hn
  nlinarith

theorem etaleThetaTruncOneSided_coeff_one_all (K : Type u) [Field K]
    (N : Nat) (hN : 1 <= N) :
    (etaleThetaTruncOneSided K N).coeff (thetaQExponent 1) =
      HahnSeries.single (thetaUExponent 1) (-1 : K) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp [etaleThetaTruncOneSided, thetaQExponent, thetaUExponent]
        norm_num
      · have hNpos : 1 <= N := by omega
        rw [etaleThetaTruncOneSided_succ, HahnSeries.coeff_add, ih hNpos]
        have hz : (thetaTermEx K (N + 1 : Int)).coeff (thetaQExponent 1) = 0 := by
          have hn : 2 <= (N + 1 : Int) := by omega
          simp [thetaTermEx, HahnSeries.coeff_single,
            thetaQExponent_ne_one_of_ge_two hn]
        rw [hz, add_zero]

#check etaleThetaTruncOneSided_coeff_one_all

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffOneAllAdapted
