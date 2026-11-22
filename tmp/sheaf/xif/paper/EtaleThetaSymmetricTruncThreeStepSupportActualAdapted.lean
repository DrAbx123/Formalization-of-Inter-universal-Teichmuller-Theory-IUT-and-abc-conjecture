import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncThreeStepSupportActualAdapted

universe u

theorem etaleThetaSymmetricTrunc_succ_three (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 3) =
      ((etaleThetaSymmetricTrunc K N + thetaPairTerm K (N + 1 : Int)) +
        thetaPairTerm K (N + 2 : Int)) + thetaPairTerm K (N + 3 : Int) := by
  rw [show N + 3 = ((N + 1) + 1) + 1 by ring]
  rw [etaleThetaSymmetricTrunc_succ, etaleThetaSymmetricTrunc_succ,
    etaleThetaSymmetricTrunc_succ]

theorem thetaPairTerm_support_singleton (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).support ⊆ ({thetaQExponent n} : Set HalfInt) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset h)
  · exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset h)

theorem etaleThetaSymmetricTrunc_three_step_diff_support (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K (N + 3) - etaleThetaSymmetricTrunc K N).support ⊆
      ({thetaQExponent (N + 1 : Int), thetaQExponent (N + 2 : Int),
        thetaQExponent (N + 3 : Int)} : Set HalfInt) := by
  have hdiff :
      (((etaleThetaSymmetricTrunc K N + thetaPairTerm K (N + 1 : Int)) +
        thetaPairTerm K (N + 2 : Int)) + thetaPairTerm K (N + 3 : Int)) -
        etaleThetaSymmetricTrunc K N =
      (thetaPairTerm K (N + 1 : Int) + thetaPairTerm K (N + 2 : Int)) +
        thetaPairTerm K (N + 3 : Int) := by
    abel
  rw [etaleThetaSymmetricTrunc_succ_three, hdiff]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · rcases HahnSeries.support_add_subset _ _ h with h | h
    · rcases thetaPairTerm_support_singleton K (N + 1 : Int) h with h'
      rw [Set.mem_singleton_iff] at h'
      rw [h']
      simp
    · rcases thetaPairTerm_support_singleton K (N + 2 : Int) h with h'
      rw [Set.mem_singleton_iff] at h'
      rw [h']
      simp
  · rcases thetaPairTerm_support_singleton K (N + 3 : Int) h with h'
    rw [Set.mem_singleton_iff] at h'
    rw [h']
    simp

theorem etaleThetaSymmetricTrunc_three_step_diff_coeff_eq_zero
    (K : Type u) [Field K] (N : Nat) (e : HalfInt)
    (h1 : e ≠ thetaQExponent (N + 1 : Int))
    (h2 : e ≠ thetaQExponent (N + 2 : Int))
    (h3 : e ≠ thetaQExponent (N + 3 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 3) - etaleThetaSymmetricTrunc K N).coeff e = 0 := by
  have hsub := etaleThetaSymmetricTrunc_three_step_diff_support K N
  have hnot : e ∉ (etaleThetaSymmetricTrunc K (N + 3) - etaleThetaSymmetricTrunc K N).support := by
    intro hmem
    have hmem' := hsub hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem'
    rcases hmem' with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  by_contra hc
  exact hnot ((HahnSeries.mem_support _ _).2 hc)

theorem etaleThetaSymmetricTrunc_three_step_stable
    (K : Type u) [Field K] (N : Nat) (e : HalfInt)
    (h1 : e ≠ thetaQExponent (N + 1 : Int))
    (h2 : e ≠ thetaQExponent (N + 2 : Int))
    (h3 : e ≠ thetaQExponent (N + 3 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 3)).coeff e =
      (etaleThetaSymmetricTrunc K N).coeff e := by
  have hz := etaleThetaSymmetricTrunc_three_step_diff_coeff_eq_zero K N e h1 h2 h3
  rw [HahnSeries.coeff_sub] at hz
  exact sub_eq_zero.mp hz

#check etaleThetaSymmetricTrunc_three_step_diff_support
#check etaleThetaSymmetricTrunc_three_step_diff_coeff_eq_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncThreeStepSupportActualAdapted
