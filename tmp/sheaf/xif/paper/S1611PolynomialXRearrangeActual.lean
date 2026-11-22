import tmp.sheaf.xif.paper.S1610PolyToFieldPolynomialXActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1611PolynomialXRearrangeActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open LeanFormal.IUT.XiFPaper.S1608SlopeOneEqExplicitActual
open LeanFormal.IUT.XiFPaper.S1610PolyToFieldPolynomialXActual

/-- polynomialX inner rearrangement. -/
theorem s1611_polynomialX_rearrange :
    (C (C 3 * X ^ 2 + C (2 * curve.toAffine.a₂) * X + C curve.toAffine.a₄) : Poly)
      = C X ^ 2 * 3 + C X * C (C curve.toAffine.a₂) * 2 + C (C curve.toAffine.a₄) := by
  simp only [C_add, C_mul, C_pow, map_ofNat, map_mul]
  ring

theorem s1611_slopeOne_eq : S1608SlopeOneEq := by
  unfold S1608SlopeOneEq slopeOne
  change pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1) =
    -polyToField curve.toAffine.polynomialX / ψᵤ 2
  rw [Affine.slope_of_Y_ne rfl s1606_smulY_one_ne_negY,
    s1606_smulY_one_sub_negY, Affine.polynomialX]
  rw [s1611_polynomialX_rearrange]
  rw [show (C (C curve.toAffine.a₁) * Y -
      (C X ^ 2 * 3 + C X * C (C curve.toAffine.a₂) * 2 + C (C curve.toAffine.a₄)) : Poly)
      = C (C curve.toAffine.a₁) * Y - C X ^ 2 * 3
        - C X * C (C curve.toAffine.a₂) * 2 - C (C curve.toAffine.a₄) by ring]
  rw [show (C (C curve.toAffine.a₁) * Y - C X ^ 2 * 3
      - C X * C (C curve.toAffine.a₂) * 2 - C (C curve.toAffine.a₄) : Poly)
      = C (C curve.toAffine.a₁) * Y - C X * C (C curve.toAffine.a₂) * 2
        - C X ^ 2 * 3 - C (C curve.toAffine.a₄) by ring]
  rw [s1610PolyToFieldPolynomialX]
  rw [s1605_pointedCurve_a1, s1606_pointedCurve_a2, s1606_pointedCurve_a4]
  ring

end LeanFormal.IUT.XiFPaper.S1611PolynomialXRearrangeActual
end