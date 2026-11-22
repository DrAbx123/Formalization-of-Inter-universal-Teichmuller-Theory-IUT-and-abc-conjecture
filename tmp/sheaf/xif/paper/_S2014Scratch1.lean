
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient

noncomputable section
open Matrix
namespace Scratch

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev V2 := Fin 2 → K5

example (g : GL2) (v : V2) (w : V2) (h : v = w) : g • v = g • w := by rw [h]

-- check coercion and det
example (g : GL2) : (g : Matrix (Fin 2) (Fin 2) K5) = g.val := rfl

-- GL is units?
example : GL2 = (Matrix (Fin 2) (Fin 2) K5)ˣ := rfl

-- Cayley-Hamilton entry form: g^2 = trace g • g - det g • 1
example (M : Matrix (Fin 2) (Fin 2) K5) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K5) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.det_fin_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.one_apply]
  all_goals ring

end Scratch
