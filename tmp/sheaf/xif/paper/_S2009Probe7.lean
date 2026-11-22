import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace S2009Probe7

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev V2 := Fin 2 → K5

theorem mulVec_fin_two_local (m : Matrix (Fin 2) (Fin 2) K5) (v : V2) :
    m *ᵥ v = ![m 0 0 * v 0 + m 0 1 * v 1, m 1 0 * v 0 + m 1 1 * v 1] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def toE0Matrix (v : V2) : Matrix (Fin 2) (Fin 2) K5 :=
  if h : v 0 = 0 then !![0, (v 1)⁻¹; -v 1, 0]
  else !![(v 0)⁻¹, 0; -v 1, v 0]

theorem toE0Matrix_det (v : V2) (hv : v ≠ 0) : (toE0Matrix v).det ≠ 0 := by
  unfold toE0Matrix
  split_ifs with h0
  · have hv1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    rw [Matrix.det_fin_two]
    simp [h0, hv1]
  · rw [Matrix.det_fin_two]
    simp [h0]

def toE0 (v : V2) (hv : v ≠ 0) : GL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (toE0Matrix v) (toE0Matrix_det v hv)

theorem toE0_smul (v : V2) (hv : v ≠ 0) : toE0 v hv • v = ![1, 0] := by
  ext i
  fin_cases i
  · show (toE0Matrix v *ᵥ v) 0 = (![1, 0] : V2) 0
    unfold toE0Matrix
    split_ifs with h0
    · have hv1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        funext j
        fin_cases j <;> simp [h0, h1]
      rw [mulVec_fin_two_local]
      simp [h0, inv_mul_cancel₀ hv1]
    · rw [mulVec_fin_two_local]
      simp [h0, inv_mul_cancel₀ h0]
  · show (toE0Matrix v *ᵥ v) 1 = (![1, 0] : V2) 1
    unfold toE0Matrix
    split_ifs with h0
    · rw [mulVec_fin_two_local]
      simp [h0]
    · rw [mulVec_fin_two_local]
      simp [h0]
      ring

end S2009Probe7