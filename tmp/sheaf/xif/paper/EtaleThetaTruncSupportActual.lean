import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncSupportActual

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def etaleThetaTruncOneSided (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaTermEx K (k : Int))

theorem thetaTermEx_support (K : Type u) [Field K] (n : Int) :
    (thetaTermEx K n).support ⊆ ({thetaQExponent n} : Set HalfInt) := by
  unfold thetaTermEx
  intro x hx
  exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset hx)

theorem thetaTermEx_support_finite (K : Type u) [Field K] (n : Int) :
    (thetaTermEx K n).support.Finite :=
  Set.Finite.subset (Set.finite_singleton (thetaQExponent n)) (thetaTermEx_support K n)

theorem support_finset_sum_finite (K : Type u) [Field K]
    (s : Finset Nat) (f : Nat -> HahnSeries HalfInt (HahnSeries Int K))
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

theorem etaleThetaTruncOneSided_support_finite (K : Type u) [Field K] (N : Nat) :
    (etaleThetaTruncOneSided K N).support.Finite := by
  unfold etaleThetaTruncOneSided
  exact support_finset_sum_finite K (Finset.range (N+1))
    (fun k => thetaTermEx K (k : Int))
    (fun k => thetaTermEx_support_finite K (k : Int))

#check etaleThetaTruncOneSided_support_finite

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncSupportActual
