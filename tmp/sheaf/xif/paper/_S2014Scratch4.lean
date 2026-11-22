
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace Scratch4

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev Mat := Matrix (Fin 2) (Fin 2) K5
abbrev V2 := Fin 2 → K5

theorem cube_roots (x : K5) (h : x^3 = 1) : x = 1 := by revert h; generalize x = y; decide
theorem cube_roots_neg (x : K5) (h : x^3 = -1) : x = -1 := by revert h; generalize x = y; decide
theorem sq_add_self_add_one_ne (x : K5) : x^2 + x + 1 ≠ 0 := by revert x; decide

theorem scalar_cube (c : K5) :
    (c • (1 : Mat)) * (c • (1 : Mat)) * (c • (1 : Mat)) = (c^3) • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem charpoly_step (M : Mat) :
    M * M = M.trace • M - M.det • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.det_fin_two, Matrix.one_apply]
  all_goals ring

theorem mat_sq_add_self_add_one (M : Mat) (h3 : M * M * M = 1) (h1 : M ≠ 1) :
    M * M + M + 1 = 0 := by
  have hCH := charpoly_step M
  have hstep : (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Mat) = 1 := by
    calc (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Mat)
        = M.trace • (M.trace • M - M.det • (1 : Mat)) - M.det • M := by
          rw [smul_sub, smul_smul, smul_smul]; abel
      _ = M.trace • (M * M) - M.det • M := by rw [hCH]
      _ = M * M * M := by
          rw [hCH]; rw [smul_sub, smul_smul, smul_smul]; abel
      _ = 1 := h3
  have hkey : (M.trace^2 - M.det) • M = (1 + M.trace * M.det) • (1 : Mat) := by
    have h := hstep
    rw [sub_eq_iff_eq_add] at h
    rw [add_comm] at h
    rw [h, add_comm]
  by_cases htd : M.trace^2 - M.det = 0
  · -- then 1 + t*d = 0, so t^3 = -1, t = -1 and d = 1
    have h2 : 1 + M.trace * M.det = 0 := by
      have h := hkey
      rw [htd, zero_smul] at h
      have := congrFun (congrFun h.symm 0) 0
      simpa using this
    have ht3 : M.trace^3 = -1 := by
      rw [htd] at h2
      linear_combination h2
    have ht : M.trace = -1 := cube_roots_neg _ ht3
    have hd : M.det = 1 := by rw [← htd, ht]; decide
    rw [hCH, ht, hd, neg_smul, one_smul]
    abel
  · exfalso
    -- M is scalar
    have hMsc : M = ((1 + M.trace * M.det) / (M.trace^2 - M.det)) • (1 : Mat) := by
      rw [eq_comm, div_eq_inv_mul, smul_smul, ← hkey, smul_smul, inv_mul_cancel₀ htd, one_smul]
    set c : K5 := (1 + M.trace * M.det) / (M.trace^2 - M.det) with hc
    have hcu : (c • (1 : Mat)) * (c • (1 : Mat)) * (c • (1 : Mat)) = 1 := by
      rw [← hMsc]; exact h3
    have hc3 : c^3 = 1 := by
      have h := hcu
      rw [scalar_cube] at h
      have := congrFun (congrFun h 0) 0
      simpa using this
    have hcone : c = 1 := cube_roots c hc3
    have hM1 : M = 1 := by rw [hMsc, hcone, one_smul]
    exact h1 hM1

end Scratch4
