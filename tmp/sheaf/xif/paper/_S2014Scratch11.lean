
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace Scratch11

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev Mat := Matrix (Fin 2) (Fin 2) K5
abbrev V2 := Fin 2 → K5

def e1v : V2 := ![1, 0]
def e2v : V2 := ![0, 1]

example (z M : Mat) (v : V2) : z *ᵥ (M *ᵥ v) = (z * M) *ᵥ v := (Matrix.mulVec_mulVec ..).symm

example (M : Mat) : (M *ᵥ e1v) 0 = M 0 0 := by
  simp [e1v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example (M : Mat) : (M *ᵥ e1v) 1 = M 1 0 := by
  simp [e1v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example (M : Mat) (c : K5) (hc : c ≠ 0) :
    (-(M 0 0) * c⁻¹) • e1v + (c⁻¹) • (M *ᵥ e1v) = e2v := by
  ext j
  fin_cases j
  · simp [e2v, e1v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
  · simp [e2v, e1v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [inv_mul_cancel₀ hc]
    ring

example (x : Mat) : (x 0 0 - (x 1 0 * (1:K5)⁻¹) * 0, x 1 0 * (1:K5)⁻¹) = (x 0 0, x 1 0) := by
  simp

end Scratch11
