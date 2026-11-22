
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

noncomputable section
open Matrix
namespace Scratch12

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev Mat := Matrix (Fin 2) (Fin 2) K5

example (M : Mat) (a b : K5) :
    (a • (1 : Mat) + b • M) = !![a + b * M 0 0, b * M 0 1; b * M 1 0, a + b * M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]

example (M : Mat) (a b : K5) :
    (a • (1 : Mat) + b • M).det = (a + b * M 0 0) * (a + b * M 1 1) - (b * M 0 1) * (b * M 1 0) := by
  rw [show (a • (1 : Mat) + b • M) = !![a + b * M 0 0, b * M 0 1; b * M 1 0, a + b * M 1 1] from by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]]
  rw [Matrix.det_fin_two]
  simp

example (M : Mat) (hM : M * M + M + 1 = 0) : M * M * M = 1 := by
  have e : M * M = -(M + 1) := by linear_combination hM
  calc M * M * M = (-(M + 1)) * M := by rw [e]
    _ = -(M * M + M) := by rw [neg_mul, add_mul, one_mul]
    _ = -((-(M + 1)) + M) := by rw [e]
    _ = 1 := by module

example (M : Mat) (a b : K5) (htr : M 0 0 + M 1 1 = -1)
    (hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) :
    (a + b * M 0 0) * (a + b * M 1 1) - (b * M 0 1) * (b * M 1 0) = a^2 - a*b + b^2 := by
  linear_combination (a*b) * htr + b^2 * hdet'

end Scratch12
