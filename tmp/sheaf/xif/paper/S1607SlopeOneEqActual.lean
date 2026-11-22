import tmp.sheaf.xif.paper.S1606SlopeDoublingActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1607SlopeOneEqActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual

/-- Exact closed-form slope target. -/
def S1607SlopeOneEq : Prop :=
  slopeOne = -polyToField curve.toAffine.polynomialX / ψᵤ 2

/-- Exact doubling base target. -/
def S1607AddXSmulOne : Prop :=
  pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2

def S1607AddYSmulOne : Prop :=
  pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2

end LeanFormal.IUT.XiFPaper.S1607SlopeOneEqActual
end