import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeSqrt

theorem adjoin_sq_finrank_dvd_two {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) (c : K) (hx : x ^ 2 = algebraMap K L c) :
    Module.finrank K (IntermediateField.adjoin K {x}) ∣ 2 := by
  have hx' : aeval x (X ^ 2 - C c : K[X]) = 0 := by
    simp [hx]
  have hmonic : (X ^ 2 - C c : K[X]).Monic := monic_X_pow_sub_C c (by norm_num)
  have hint : IsIntegral K x := ⟨_, hmonic, hx'⟩
  have hdvd : minpoly K x ∣ X ^ 2 - C c := minpoly.dvd K x hx'
  have hle : (minpoly K x).natDegree ≤ 2 := by
    have h := natDegree_le_of_dvd hdvd hmonic.ne_zero
    simpa [natDegree_X_pow_sub_C] using h
  have hpos : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos hint
  have hdeg : (minpoly K x).natDegree ∣ 2 := by
    interval_cases h : (minpoly K x).natDegree <;> norm_num
  rw [IntermediateField.adjoin.finrank hint]
  exact hdeg

end ProbeSqrt
