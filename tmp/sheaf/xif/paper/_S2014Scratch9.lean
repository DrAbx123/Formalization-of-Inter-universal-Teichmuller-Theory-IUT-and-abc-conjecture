
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace Scratch9

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev Mat := Matrix (Fin 2) (Fin 2) K5
abbrev V2 := Fin 2 → K5

example (g : GL2) : (↑(g^3) : Mat) = (↑g : Mat)^3 := map_pow (Units.coeHom Mat) g 3

example (g : GL2) (hg : g ≠ 1) : (↑g : Mat) ≠ 1 := by
  intro h
  apply hg
  exact Units.ext h

-- entries of a matrix from the relation
example (M : Mat) (h : M * M + M + 1 = 0) :
    (M 0 0)^2 + (M 0 1) * (M 1 0) + M 0 0 + 1 = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h00

example (M : Mat) (h : M * M + M + 1 = 0) :
    (M 1 0) * (M 0 0) + (M 1 1) * (M 1 0) + M 1 0 = 0 := by
  have h10 := congrFun (congrFun h 1) 0
  simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h10

-- c = M 1 0 ≠ 0
example (M : Mat) (h : M * M + M + 1 = 0) : M 1 0 ≠ 0 := by
  intro hc
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hc] at h00
  exact absurd h00 (by revert h00; generalize M 0 0 = x; decide)

-- trace relation
example (M : Mat) (h : M * M + M + 1 = 0) : M 0 0 + M 1 1 + 1 = 0 := by
  have hc : M 1 0 ≠ 0 := by
    intro hc
    have h00 := congrFun (congrFun h 0) 0
    simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hc] at h00
    exact absurd h00 (by revert h00; generalize M 0 0 = x; decide)
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
    Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply] at h10
  -- h10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 + M 1 0 = 0
  have : M 1 0 * (M 0 0 + M 1 1 + 1) = 0 := by linear_combination h10
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hc
  · exact h'

end Scratch9
