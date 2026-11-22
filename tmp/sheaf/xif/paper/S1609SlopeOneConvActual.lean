import tmp.sheaf.xif.paper.S1608SlopeOneEqExplicitActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1609SlopeOneConvActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open LeanFormal.IUT.XiFPaper.S1608SlopeOneEqExplicitActual

/-- Exact slope target; conv_rhs expansion is the remaining formal step. -/
def S1609SlopeOneEq : Prop :=
  slopeOne = -polyToField curve.toAffine.polynomialX / ψᵤ 2

end LeanFormal.IUT.XiFPaper.S1609SlopeOneConvActual
end