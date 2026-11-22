import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSupportFiniteActual

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

theorem thetaPairTerm_support (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).support ⊆ ({thetaQExponent n} : Set HalfInt) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset h)
  · exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset h)

theorem thetaPairTerm_support_finite (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).support.Finite :=
  Set.Finite.subset (Set.finite_singleton (thetaQExponent n)) (thetaPairTerm_support K n)

noncomputable def etaleThetaSymmetricTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaPairTerm K (k : Int))

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

theorem etaleThetaSymmetricTrunc_support_finite (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K N).support.Finite := by
  unfold etaleThetaSymmetricTrunc
  exact support_finset_sum_finite K (Finset.range (N+1))
    (fun k => thetaPairTerm K (k : Int))
    (fun k => thetaPairTerm_support_finite K (k : Int))

#check etaleThetaSymmetricTrunc_support_finite

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSupportFiniteActual
