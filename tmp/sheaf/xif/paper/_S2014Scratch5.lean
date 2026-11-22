
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace Scratch5

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
  rw [sub_mul, Matrix.smul_mul, Matrix.one_mul, charpoly_step M, smul_sub, smul_smul, smul_smul]
  module

theorem mat_sq_add_self_add_one (M : Mat) (h3 : M * M * M = 1) (h1 : M ≠ 1) :
    M * M + M + 1 = 0 := by
  have hexp := cube_expand M
  rw [h3] at hexp
  -- hexp : 1 = (t^2 - d) • M - (t*d) • 1
  by_cases htd : M.trace^2 - M.det = 0
  · have h2 : M.trace * M.det = -1 := by
      have h := hexp
      rw [htd, zero_smul, zero_sub] at h
      -- h : 1 = -((t*d) • 1)
      have := congrFun (congrFun h 0) 0
      simp [Matrix.smul_apply, Matrix.one_apply] at this
      linear_combination -this
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
    have hMsc : M = (((M.trace^2 - M.det)⁻¹ * (1 + M.trace * M.det))) • (1 : Mat) := by
      have h := hexp
      rw [sub_eq_iff_eq_add] at h
      -- h : 1 = -((t*d) • 1) + (t^2-d) • M
      have h2 : ((M.trace^2 - M.det)⁻¹) • (1 : Mat)
          = ((M.trace^2 - M.det)⁻¹) • (-((M.trace * M.det) • (1 : Mat)) + (M.trace^2 - M.det) • M) := by
        rw [h]
      rw [smul_add, smul_neg, smul_smul, smul_smul, inv_mul_cancel₀ htd, one_smul, one_smul] at h2
      rw [eq_comm] at h2
      calc M = 1 • M + 0 := by rw [one_smul, add_zero]
        _ = 1 • M + (-(((M.trace: K5)) * M.det • (1 : Mat)) + (M.trace * M.det) • (1 : Mat)) := by
            rw [neg_add_cancel]
        _ = 1 • M + (M.trace^2 - M.det)⁻¹ • (1:Mat) - (M.trace^2 - M.det)⁻¹ • (M.trace * M.det) • (1:Mat) := by
            module
        _ = _ := by
            have := h2
            sorry
    sorry

end Scratch5
