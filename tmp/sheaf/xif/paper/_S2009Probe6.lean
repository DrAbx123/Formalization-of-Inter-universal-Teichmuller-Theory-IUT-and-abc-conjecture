import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

noncomputable section
open Matrix
namespace S2009Probe6

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev V2 := Fin 2 → K5

#check @Matrix.mulVec_eq_sum
#check @Matrix.cons_val_zero
#check @Matrix.cons_val_one

theorem mulVec_fin_two_local (m : Matrix (Fin 2) (Fin 2) K5) (v : V2) :
    m *ᵥ v = ![m 0 0 * v 0 + m 0 1 * v 1, m 1 0 * v 0 + m 1 1 * v 1] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example : ((![1, 0] : V2) 0) = 1 := by simp
example : ((![1, 0] : V2) 1) = 0 := by simp
example (a b : K5) : ((!![a, b; b, a] : Matrix (Fin 2) (Fin 2) K5) *ᵥ ![1, 0]) 0 = a := by
  rw [mulVec_fin_two_local]
  simp

end S2009Probe6
