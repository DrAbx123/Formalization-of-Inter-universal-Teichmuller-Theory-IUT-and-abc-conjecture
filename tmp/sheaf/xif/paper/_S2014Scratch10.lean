
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

noncomputable section
open Matrix
namespace Scratch10

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev Mat := Matrix (Fin 2) (Fin 2) K5

example : (if (1 : Fin 2) = 0 then (1:K5) else 0) = 0 := by simp
example : (if (1 : Fin 2) = 1 then (1:K5) else 0) = 1 := by simp
example (a b c d : K5) : (!![a,b;c,d] : Mat) * !![a,b;c,d] = !![a*a+b*c, a*b+b*d; c*a+d*c, c*b+d*d] := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

example (M : Mat) (h : M * M + M + 1 = 0) : M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 0 + 1 = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h00

example (M : Mat) (h : M * M + M + 1 = 0) : M 1 0 * M 0 0 + M 1 1 * M 1 0 + M 1 0 = 0 := by
  have h10 := congrFun (congrFun h 1) 0
  simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h10

end Scratch10
