import tmp.sheaf.xif.paper.S1608SlopeOneEqExplicitActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1610PolyToFieldPolynomialXActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open LeanFormal.IUT.XiFPaper.S1608SlopeOneEqExplicitActual

/-- The polynomialX image under polyToField. -/
theorem s1610PolyToFieldPolynomialX :
    polyToField (C (C curve.toAffine.a₁) * Y - C X * C (C curve.toAffine.a₂) * 2
      - C X ^ 2 * 3 - C (C curve.toAffine.a₄)) =
      polyToField (C (C curve.toAffine.a₁)) * smulY 1
        - 2 * polyToField (C (C curve.toAffine.a₂)) * smulX 1
        - 3 * smulX 1 ^ 2 - polyToField (C (C curve.toAffine.a₄)) := by
  rw [map_sub polyToField, map_sub polyToField, map_sub polyToField]
  rw [map_mul polyToField, map_mul polyToField, map_mul polyToField,
    map_mul polyToField, map_pow polyToField]
  rw [s1608_polyToField_CC, s1608_polyToField_CX, s1608_polyToField_X]
  simp only [map_ofNat]
  ring

/-- Exact slope target; polynomialX shape mismatch remains. -/
def S1610SlopeOneEq : Prop :=
  slopeOne = -polyToField curve.toAffine.polynomialX / ψᵤ 2

end LeanFormal.IUT.XiFPaper.S1610PolyToFieldPolynomialXActual
end