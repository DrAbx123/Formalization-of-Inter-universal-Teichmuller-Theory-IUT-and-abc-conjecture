
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace Scratch2

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev V2 := Fin 2 → K5

theorem cube_roots (x : K5) (h : x^3 = 1) : x = 1 := by revert h; generalize x = y; decide

theorem cube_roots_neg (x : K5) (h : x^3 = -1) : x = -1 := by revert h; generalize x = y; decide

theorem sq_ne (x : K5) : x^2 + x + 1 ≠ 0 := by revert x; decide

theorem charpoly_of_order_three (g : GL2) (hg : orderOf g = 3) :
    (g : Matrix (Fin 2) (Fin 2) K5) * g + (g : Matrix (Fin 2) (Fin 2) K5) + 1 = 0 := by
  have hg3 : g^3 = 1 := by
    rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h; rw [h] at hg; simp at hg
  set M : Matrix (Fin 2) (Fin 2) K5 := (g : Matrix (Fin 2) (Fin 2) K5) with hMdef
  have hcube : M * M * M = 1 := by
    have : (↑(g^3) : Matrix (Fin 2) (Fin 2) K5) = 1 := by rw [hg3]; simp
    rwa [map_pow, pow_three] at this
  have hCH : M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K5) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.det_fin_two, Matrix.one_apply]
    all_goals ring
  -- derive (t^2 - d) • M = (1 + t*d) • 1
  have hstep : (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Matrix (Fin 2) (Fin 2) K5) = 1 := by
    calc (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Matrix (Fin 2) (Fin 2) K5)
        = M.trace • (M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K5)) - M.det • M := by
          module
      _ = M.trace • (M * M) - M.det • M := by rw [hCH]
      _ = M * M * M := by
          rw [hCH]
          module
      _ = 1 := hcube
  have hkey : (M.trace^2 - M.det) • M = (1 + M.trace * M.det) • (1 : Matrix (Fin 2) (Fin 2) K5) := by
    rw [← sub_eq_iff_eq_add] at hstep ⊢
    rw [hstep]; abel
  -- case split on t^2 = d
  by_cases htd : M.trace^2 - M.det = 0
  · have ht3 : M.trace^3 = -1 := by
      have h1 : (1 + M.trace * M.det) • (1 : Matrix (Fin 2) (Fin 2) K5) = 0 := by
        rw [← hkey, htd]; simp
      have h2 : (1 + M.trace * M.det) = 0 := by
        have := congrFun (congrFun (Subsingleton.elim _ _ ▸ h1) 0) 0
        simpa using this
      rw [htd] at h2
      linear_combination h2
    have ht : M.trace = -1 := cube_roots_neg _ ht3
    have hd : M.det = 1 := by rw [← htd, ht]; decide
    rw [← hCH, ht, hd]
    simp
  · exfalso
    have hinv : M = ((1 + M.trace * M.det) / (M.trace^2 - M.det)) • (1 : Matrix (Fin 2) (Fin 2) K5) := by
      rw [eq_comm, smul_eq_mul, ← hkey, smul_smul, mul_inv_cancel₀ htd]
      simp
    -- M scalar implies M = 1 (since M^3 = 1) implies g = 1, contradicting order 3
    have hsc : ∀ i j : Fin 2, M i j = if i = j then ((1 + M.trace * M.det) / (M.trace^2 - M.det)) else 0 := by
      intro i j
      rw [hinv]
      simp [Matrix.smul_apply, Matrix.one_apply]
    have hM1 : M = (1 : Matrix (Fin 2) (Fin 2) K5) := by
      have hc3 : ((1 + M.trace * M.det) / (M.trace^2 - M.det))^3 = 1 := by
        have h := hcube
        rw [hinv] at h
        have : (((1 + M.trace * M.det) / (M.trace^2 - M.det))^3) • (1 : Matrix (Fin 2) (Fin 2) K5) = 1 := by
          calc (((1 + M.trace * M.det) / (M.trace^2 - M.det))^3) • (1 : Matrix (Fin 2) (Fin 2) K5)
              = (((1 + M.trace * M.det) / (M.trace^2 - M.det)) • (1 : Matrix (Fin 2) (Fin 2) K5)) *
                (((1 + M.trace * M.det) / (M.trace^2 - M.det)) • (1 : Matrix (Fin 2) (Fin 2) K5)) *
                (((1 + M.trace * M.det) / (M.trace^2 - M.det)) • (1 : Matrix (Fin 2) (Fin 2) K5)) := by
                  module
            _ = 1 := h
        have := congrFun (congrFun this 0) 0
        simpa using this
      have hc : ((1 + M.trace * M.det) / (M.trace^2 - M.det)) = 1 := cube_roots _ hc3
      rw [hinv, hc, one_smul]
    have : g = 1 := by
      apply Units.ext
      rw [← hMdef]
      exact hM1
    rw [this] at hg; simp at hg

end Scratch2
