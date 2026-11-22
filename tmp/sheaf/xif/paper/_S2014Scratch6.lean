
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace Scratch6

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev Mat := Matrix (Fin 2) (Fin 2) K5
abbrev V2 := Fin 2 → K5

theorem cube_roots : ∀ x : K5, x^3 = 1 → x = 1 := by decide
theorem cube_roots_neg : ∀ x : K5, x^3 = -1 → x = -1 := by decide
theorem sq_add_self_add_one_ne : ∀ x : K5, x^2 + x + 1 ≠ 0 := by decide

theorem scalar_cube (c : K5) :
    (c • (1 : Mat)) * (c • (1 : Mat)) * (c • (1 : Mat)) = (c^3) • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem charpoly_step (M : Mat) :
    M * M = M.trace • M - M.det • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.det_fin_two, Matrix.one_apply]
  all_goals ring

theorem cube_expand (M : Mat) :
    M * M * M = (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Mat) := by
  conv_lhs => rw [charpoly_step M]
  rw [sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, charpoly_step M,
    smul_sub, smul_smul, smul_smul]
  module

theorem mat_sq_add_self_add_one (M : Mat) (h3 : M * M * M = 1) (h1 : M ≠ 1) :
    M * M + M + 1 = 0 := by
  have hexp : (1 : Mat) = (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Mat) := by
    rw [← cube_expand M, h3]
  by_cases htd : M.trace^2 - M.det = 0
  · have h2 : M.trace * M.det = -1 := by
      have h := hexp
      rw [htd, zero_smul, zero_sub] at h
      have e := congrFun (congrFun h 0) 0
      simp [Matrix.smul_apply] at e
      rw [← e]; ring
    have hd : M.det = M.trace^2 := by linear_combination -htd
    have ht3 : M.trace^3 = -1 := by
      rw [hd] at h2
      linear_combination h2
    have ht : M.trace = -1 := cube_roots_neg _ ht3
    have hd1 : M.det = 1 := by rw [hd, ht]; decide
    have hCH := charpoly_step M
    rw [hCH, ht, hd1]
    module
  · exfalso
    have hMsc : M = ((M.trace^2 - M.det)⁻¹ * (1 + M.trace * M.det)) • (1 : Mat) := by
      have h1 : ((M.trace^2 - M.det)⁻¹) • (1 : Mat)
          = M - ((M.trace^2 - M.det)⁻¹ * (M.trace * M.det)) • (1 : Mat) := by
        calc ((M.trace^2 - M.det)⁻¹) • (1 : Mat)
            = ((M.trace^2 - M.det)⁻¹) • ((M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Mat)) := by
              rw [hexp]
          _ = ((M.trace^2 - M.det)⁻¹ * (M.trace^2 - M.det)) • M
                - ((M.trace^2 - M.det)⁻¹ * (M.trace * M.det)) • (1 : Mat) := by
              rw [smul_sub, smul_smul, smul_smul]
          _ = M - ((M.trace^2 - M.det)⁻¹ * (M.trace * M.det)) • (1 : Mat) := by
              rw [inv_mul_cancel₀ htd, one_smul]
      have h2 : M = ((M.trace^2 - M.det)⁻¹) • (1 : Mat)
          + ((M.trace^2 - M.det)⁻¹ * (M.trace * M.det)) • (1 : Mat) := by
        rw [h1]; abel
      rw [h2, ← add_smul]
      congr 1
      ring
    set c : K5 := (M.trace^2 - M.det)⁻¹ * (1 + M.trace * M.det) with hc
    have hcube' : (c • (1 : Mat)) * (c • (1 : Mat)) * (c • (1 : Mat)) = 1 := by
      rw [← hMsc]; exact h3
    have hc3 : c^3 = 1 := by
      rw [scalar_cube] at hcube'
      have e := congrFun (congrFun hcube' 0) 0
      simpa using e
    have hcone : c = 1 := cube_roots c hc3
    have hM1 : M = 1 := by rw [hMsc, hcone, one_smul]
    exact h1 hM1

end Scratch6
