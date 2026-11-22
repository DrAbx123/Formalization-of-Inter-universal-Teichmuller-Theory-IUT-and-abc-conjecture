import tmp.sheaf.xif.paper.S1604AffineGroupLawIntegratedActual
import tmp.sheaf.xif.paper.S1593ZSMulFieldActual
import tmp.sheaf.xif.paper.S1598PolyToFieldCCActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual

/-- pointedCurve a1 coefficient equals polyToField of CC curve.a1. -/
theorem s1605_pointedCurve_a1 :
    pointedCurve.toAffine.a₁ = polyToField (CC curve.a₁) := by
  rw [pointedCurve, curvePoly, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₁]
  exact s1598PolyToField_CC curve.a₁

/-- pointedCurve a3 coefficient equals polyToField of CC curve.a3. -/
theorem s1605_pointedCurve_a3 :
    pointedCurve.toAffine.a₃ = polyToField (CC curve.a₃) := by
  rw [pointedCurve, curvePoly, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₃]
  exact s1598PolyToField_CC curve.a₃


/-- TauCeti smulY_sub_negY, using the two coefficient exchange lemmas. -/
theorem s1605_smulY_sub_negY (n : Int) (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) =
      ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  have hψ : ψᵤ n ≠ 0 := polyToField_ψ_ne_zero n h0
  have h : curve.ψ n * (2 * curve.ω n + CC curve.a₁ * curve.φ n * curve.ψ n
      + CC curve.a₃ * curve.ψ n ^ 3) = curve.ψ (2 * n) := by
    rw [WeierstrassCurve.ω_spec, WeierstrassCurve.ψ_mul_ψc]
  have hF := congrArg polyToField h
  simp only [map_mul, map_add, map_pow, map_ofNat] at hF
  rw [show smulY n = polyToField (curve.ω n) / (polyToField (curve.ψ n)) ^ 3 from rfl,
    show smulX n = polyToField (curve.φ n) / (polyToField (curve.ψ n)) ^ 2 from rfl]
  rw [Affine.negY, s1605_pointedCurve_a1, s1605_pointedCurve_a3]
  field_simp
  linear_combination hF


/-- Nonvanishing of the gap. -/
theorem s1605_smulY_ne_negY (n : Int) (h0 : n ≠ 0) :
    smulY n ≠ pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  rw [← sub_ne_zero, s1605_smulY_sub_negY n h0]
  exact div_ne_zero (polyToField_ψ_ne_zero (2 * n) (by omega))
    (pow_ne_zero _ (polyToField_ψ_ne_zero n h0))

end LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
end