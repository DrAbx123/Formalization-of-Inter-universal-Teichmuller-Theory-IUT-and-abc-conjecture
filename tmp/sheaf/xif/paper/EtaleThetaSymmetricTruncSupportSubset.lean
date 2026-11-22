import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSupportSubset

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

lemma support_finset_sum_subset (K : Type u) [Field K]
    (s : Finset Nat) (f : Nat -> HahnSeries HalfInt (HahnSeries Int K)) :
    (Finset.sum s f).support ⊆
      {x : HalfInt | exists i : Nat, i ∈ s ∧ x ∈ (f i).support} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      intro x hx
      rcases HahnSeries.support_add_subset _ _ hx with h | h
      · exact ⟨a, Finset.mem_insert_self a s, h⟩
      · rcases ih h with ⟨i, hi, hxi⟩
        exact ⟨i, Finset.mem_insert_of_mem hi, hxi⟩

noncomputable def etaleThetaSymmetricTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaPairTerm K (k : Int))

theorem etaleThetaSymmetricTrunc_support_subset (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K N).support ⊆
      {e : HalfInt | exists n : Nat, n <= N ∧ thetaQExponent (n : Int) = e} := by
  intro e he
  unfold etaleThetaSymmetricTrunc at he
  rcases support_finset_sum_subset K (Finset.range (N+1))
    (fun k => thetaPairTerm K (k : Int)) he with ⟨k, hk, hkp⟩
  have hk' : (k : Nat) <= N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsingle := thetaPairTerm_support K (k : Int) hkp
  refine ⟨k, hk', ?_⟩
  exact (Set.mem_singleton_iff.mp hsingle).symm

#check etaleThetaSymmetricTrunc_support_subset

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSupportSubset
