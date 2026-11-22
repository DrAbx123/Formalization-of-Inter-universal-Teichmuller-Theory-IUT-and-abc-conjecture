
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace Scratch3

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5

example (c : K5) : c • (1 : Matrix (Fin 2) (Fin 2) K5) = diagonal (fun _ => c) := by
  rw [Matrix.smul_one_eq_diagonal]

example (c d : K5) : diagonal (fun _ : Fin 2 => c) * diagonal (fun _ => d) = diagonal (fun _ => c*d) := by
  rw [Matrix.diagonal_mul_diagonal]; rfl

example (c : K5) : (c • (1 : Matrix (Fin 2) (Fin 2) K5)) * (c • (1 : Matrix (Fin 2) (Fin 2) K5)) *
    (c • (1 : Matrix (Fin 2) (Fin 2) K5)) = (c^3) • (1 : Matrix (Fin 2) (Fin 2) K5) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  ring

example (c : K5) (h : (c^3) • (1 : Matrix (Fin 2) (Fin 2) K5) = 1) : c^3 = 1 := by
  have h' := congrFun (congrFun h 0) 0
  simpa using h'

end Scratch3
