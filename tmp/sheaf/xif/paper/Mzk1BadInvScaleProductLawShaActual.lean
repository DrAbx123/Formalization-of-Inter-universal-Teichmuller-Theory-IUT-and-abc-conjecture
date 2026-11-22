import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! # badInvScale product law (generic coordinatewise reference) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BadInvScaleProductLawShaActual

variable {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]

/-- Coordinatewise inverse bad-prime scaling: `x i ↦ (f i)⁻¹ • x i`. -/
noncomputable def badInvScale (f : ι → Real) (x : ι → V) : ι → V :=
  fun i => (f i)⁻¹ • x i

/-- Product law: composing two inverse scalings multiplies the factors. -/
theorem badInvScale_comp (f g : ι → Real) (x : ι → V) :
    badInvScale f (badInvScale g x) =
      badInvScale (fun i => f i * g i) x := by
  funext i
  unfold badInvScale
  rw [smul_smul, mul_inv]

/-- Norm law: coordinatewise norm scales by the inverse factor. -/
theorem norm_badInvScale (f : ι → Real) (x : ι → V) (i : ι) :
    ‖badInvScale f x i‖ = ‖(f i)⁻¹‖ * ‖x i‖ := by
  unfold badInvScale
  rw [norm_smul]

#print axioms badInvScale_comp
#print axioms norm_badInvScale

end LeanFormal.IUT.XiFPaper.Mzk1BadInvScaleProductLawShaActual
