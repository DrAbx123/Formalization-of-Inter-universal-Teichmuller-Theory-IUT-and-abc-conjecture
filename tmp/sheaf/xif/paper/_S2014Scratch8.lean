
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace Scratch8

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

theorem eq_smul_one_of_smul_eq (X : Mat) (k q : K5) (hk : k ≠ 0) (h : k • X = q • (1 : Mat)) :
    X = (k⁻¹ * q) • (1 : Mat) := by
  have hh := congrArg (fun Y : Mat => k⁻¹ • Y) h
  rwa [smul_smul, inv_mul_cancel₀ hk, one_smul, smul_smul] at hh

theorem scalar_eq_one (c : K5) (X : Mat) (hX : X = c • (1 : Mat))
    (h3 : X * X * X = 1) : X = 1 := by
  have hc3 : c^3 = 1 := by
    rw [hX, scalar_cube] at h3
    have e := congrFun (congrFun h3 0) 0
    simpa using e
  have hc : c = 1 := cube_roots c hc3
  rw [hX, hc, one_smul]

theorem mat_sq_add_self_add_one (M : Mat) (h3 : M * M * M = 1) (h1 : M ≠ 1) :
    M * M + M + 1 = 0 := by
  have hexp : (1 : Mat) = (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Mat) := by
    rw [← cube_expand M, h3]
  have hkey : (M.trace^2 - M.det) • M = (1 + M.trace * M.det) • (1 : Mat) := by
    have h := hexp
    rw [eq_comm, sub_eq_iff_eq_add] at h
    rw [h]
    rw [show (1 + M.trace * M.det) • (1 : Mat) = (M.trace * M.det) • (1 : Mat) + 1 from by
      rw [add_smul, one_smul]; abel]
    abel
  by_cases htd : M.trace^2 - M.det = 0
  · have h2 : 1 + M.trace * M.det = 0 := by
      rw [htd, zero_smul] at hkey
      have e := congrFun (congrFun hkey.symm 0) 0
      simpa [Matrix.smul_apply] using e
    have hd : M.det = M.trace^2 := by linear_combination -htd
    have hl : M.trace * M.det = -1 := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      rw [← h2]
    have ht3 : M.trace^3 = -1 := by
      rw [hd] at hl
      linear_combination hl
    have ht : M.trace = -1 := cube_roots_neg _ ht3
    have hd1 : M.det = 1 := by rw [hd, ht]; decide
    have hCH := charpoly_step M
    rw [hCH, ht, hd1]
    module
  · exfalso
    refine h1 (scalar_eq_one ((M.trace^2 - M.det)⁻¹ * (1 + M.trace * M.det)) M ?_ h3)
    exact eq_smul_one_of_smul_eq M _ _ htd hkey

end Scratch8