import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncSupport

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

noncomputable def thetaTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

theorem thetaTerm_support_finite (K : Type u) [Field K] (n : Int) :
    (thetaTerm K n).support.Finite := by
  unfold thetaTerm
  refine Set.Finite.subset (Set.finite_singleton (thetaQExponent n)) ?_
  intro x hx
  exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset hx)

theorem support_finset_sum_finite (K : Type u) [Field K]
    (s : Finset Int) (f : Int -> HahnSeries HalfInt (HahnSeries Int K))
    (h : forall n, (f n).support.Finite) :
    (Finset.sum s f).support.Finite := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine Set.Finite.subset ((h a).union ih) ?_
      intro x hx
      exact HahnSeries.support_add_subset _ _ hx

noncomputable def etaleThetaTruncIcc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.Icc (-(N : Int)) (N : Int)) (fun n : Int =>
    thetaTerm K n)

theorem etaleThetaTruncIcc_support_finite (K : Type u) [Field K] (N : Nat) :
    (etaleThetaTruncIcc K N).support.Finite := by
  unfold etaleThetaTruncIcc
  exact support_finset_sum_finite K (Finset.Icc (-(N : Int)) (N : Int))
    (thetaTerm K) (thetaTerm_support_finite K)

#check etaleThetaTruncIcc_support_finite

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncSupport
