import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! # Hull scaling product law (generic normed space) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullScalingProductLawShaActual

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]

noncomputable def scaleUp (k : Nat) (x : V) : V := ((k + 1 : Real)) • x
noncomputable def scaleDown (k : Nat) (x : V) : V := ((k + 1 : Real)⁻¹) • x

/-- Product law: two upward scalings compose to the scaling with product factor. -/
theorem scaleUp_scaleUp (k l : Nat) (x : V) :
    scaleUp k (scaleUp l x) = scaleUp (k * l + k + l) x := by
  unfold scaleUp
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- Product law: two downward scalings compose to the scaling with product factor. -/
theorem scaleDown_scaleDown (k l : Nat) (x : V) :
    scaleDown k (scaleDown l x) = scaleDown (k * l + k + l) x := by
  unfold scaleDown
  rw [smul_smul]
  congr 1
  push_cast
  field_simp
  ring

/-- Norm law: upward scaling multiplies the norm by `k + 1`. -/
theorem norm_scaleUp (k : Nat) (x : V) :
    ‖scaleUp k x‖ = (k + 1 : Real) * ‖x‖ := by
  unfold scaleUp
  rw [norm_smul, Real.norm_of_nonneg]
  positivity

#print axioms scaleUp_scaleUp
#print axioms scaleDown_scaleDown
#print axioms norm_scaleUp

end LeanFormal.IUT.XiFPaper.Mzk1HullScalingProductLawShaActual
