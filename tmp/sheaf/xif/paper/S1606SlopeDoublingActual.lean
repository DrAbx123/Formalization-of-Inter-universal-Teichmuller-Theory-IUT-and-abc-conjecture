import tmp.sheaf.xif.paper.S1605PointedCurveCoeffActual
import tmp.sheaf.xif.paper.S1603AffineGroupLawActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual


theorem s1606_pointedCurve_a2 :
    pointedCurve.toAffine.a₂ = polyToField (CC curve.a₂) := by
  rw [pointedCurve, curvePoly, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₂]
  exact s1598PolyToField_CC curve.a₂

theorem s1606_pointedCurve_a4 :
    pointedCurve.toAffine.a₄ = polyToField (CC curve.a₄) := by
  rw [pointedCurve, curvePoly, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₄]
  exact s1598PolyToField_CC curve.a₄

/-- n=1 gap, derived from S1605. -/
theorem s1606_smulY_one_sub_negY :
    smulY 1 - Affine.negY (pointedCurve.toAffine) (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [s1605_smulY_sub_negY 1 one_ne_zero]
  simp [ψᵤ, WeierstrassCurve.ψ_one, mul_one]

theorem s1606_smulY_one_ne_negY :
    smulY 1 ≠ Affine.negY (pointedCurve.toAffine) (smulX 1) (smulY 1) :=
  s1605_smulY_ne_negY 1 one_ne_zero

/-- Exact slope target. -/
def S1606SlopeOneEq : Prop :=
  slopeOne = -polyToField curve.toAffine.polynomialX / ψᵤ 2

end LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
end