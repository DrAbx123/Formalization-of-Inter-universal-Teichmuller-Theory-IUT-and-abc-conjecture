import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Prime.Basic
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual

noncomputable section
set_option maxHeartbeats 4000000
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

lemma mat_sub_one_mul_add_one (M : Mat) (hM : M * M = 1) : (M - 1) * (M + 1) = 0 := by
  calc (M - 1) * (M + 1) = (M - 1) * M + (M - 1) * 1 := by rw [mul_add]
    _ = (M * M - 1 * M) + (M - 1) := by rw [sub_mul, mul_one]
    _ = (1 - M) + (M - 1) := by rw [hM, one_mul]
    _ = 0 := by abel

lemma involution_fixes_pair (A : GL2) (hA : A ^ 2 = 1) :
    ∃ x : PairRep, pairAct A x = x := by
  by_cases hA1 : A = 1
  · refine ⟨⟨![1, 0], by decide⟩, ?_⟩
    rw [hA1]
    exact pairAct_one _
  · have hM : (A : Mat) * (A : Mat) = 1 := by
      have h := congrArg (fun y : GL2 => (y : Mat)) hA
      simpa [pow_two] using h
    have hprod : ((A : Mat) - 1) * ((A : Mat) + 1) = 0 := mat_sub_one_mul_add_one (A : Mat) hM
    have hdet : ((A : Mat) - 1).det * ((A : Mat) + 1).det = 0 := by
      rw [← Matrix.det_mul, hprod, Matrix.det_zero]
    rcases mul_eq_zero.mp hdet with hd | hd
    · obtain ⟨v, hv, hAv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := (A : Mat) - 1)).mpr hd
      have hfix : (A : Mat) *ᵥ v = v := by
        have hsub : (A : Mat) *ᵥ v - v = 0 := by
          simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hAv
        exact sub_eq_zero.mp hsub
      refine ⟨⟨normalize v, normalize_isRep v hv⟩, ?_⟩
      apply Subtype.ext
      show normalize (A • normalize v) = normalize v
      rcases normalize_eq_or_neg v with hv' | hv'
      · rw [hv']
        rw [Units.smul_def, Matrix.smul_eq_mulVec, hfix]
        exact hv'
      · rw [hv']
        have hneg : (A : Mat) *ᵥ (-v) = -v := by
          rw [mulVec_neg, hfix]
        rw [Units.smul_def, Matrix.smul_eq_mulVec, hneg, normalize_neg]
        exact hv'
    · obtain ⟨v, hv, hAv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := (A : Mat) + 1)).mpr hd
      have hfix : (A : Mat) *ᵥ v = -v := by
        have hsum : (A : Mat) *ᵥ v + v = 0 := by
          simpa [Matrix.add_mulVec, Matrix.one_mulVec] using hAv
        exact eq_neg_of_add_eq_zero_left hsum
      refine ⟨⟨normalize v, normalize_isRep v hv⟩, ?_⟩
      apply Subtype.ext
      show normalize (A • normalize v) = normalize v
      rcases normalize_eq_or_neg v with hv' | hv'
      · rw [hv']
        rw [Units.smul_def, Matrix.smul_eq_mulVec, hfix, normalize_neg, hv']
      · rw [hv']
        have hneg : (A : Mat) *ᵥ (-v) = v := by
          rw [mulVec_neg, hfix, neg_neg]
        rw [Units.smul_def, Matrix.smul_eq_mulVec, hneg, hv']

end LeanFormal.IUT.XiFPaper.S2009DicksonActual