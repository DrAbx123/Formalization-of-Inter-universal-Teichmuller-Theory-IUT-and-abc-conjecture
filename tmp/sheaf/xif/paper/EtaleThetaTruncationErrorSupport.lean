import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncationErrorSupport

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

theorem etaleThetaTruncOneSided_diff (K : Type u) [Field K] (N : Nat) :
    etaleThetaTruncOneSided K (N + 1) - etaleThetaTruncOneSided K N =
      thetaTermEx K (N + 1 : Int) := by
  rw [etaleThetaTruncOneSided_succ]
  abel

theorem etaleThetaTruncOneSided_diff_support (K : Type u) [Field K] (N : Nat) :
    (etaleThetaTruncOneSided K (N + 1) - etaleThetaTruncOneSided K N).support ⊆
      ({thetaQExponent (N + 1 : Int)} : Set HalfInt) := by
  rw [etaleThetaTruncOneSided_diff]
  intro x hx
  exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset hx)

#check etaleThetaTruncOneSided_diff
#check etaleThetaTruncOneSided_diff_support

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncationErrorSupport
