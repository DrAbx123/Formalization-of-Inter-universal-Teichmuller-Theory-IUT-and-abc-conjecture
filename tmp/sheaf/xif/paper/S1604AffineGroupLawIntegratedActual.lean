import tmp.sheaf.xif.paper.S1603AffineGroupLawActual
import tmp.sheaf.xif.paper.S1597UniversalAffineFullActual

/-! # S1604: integrated affine group-law report

The TauCeti draft tmp/sheaf/xif/paper/_PRZSMul.lean contains the affine layer.
Integration attempt for smulY_sub_negY reduced to the rational identity but the
project-side pointedCurve coefficient rewrite (a1/a3) and the final ring step
did not close.  This file records the exact order; no coordinate is faked. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1604AffineGroupLawIntegratedActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual

#check S1603SmulYSubNegY
#check S1603SmulYNeNegY
#check S1603SlopeOneEq
#check S1603AddXSmulOne
#check S1603AddYSmulOne
#check S1603SmulXAdd
#check slopeOne

/-- Exact first integrated target: TauCeti smulY_sub_negY. -/
def S1604SmulYSubNegY : Prop := S1603SmulYSubNegY

end LeanFormal.IUT.XiFPaper.S1604AffineGroupLawIntegratedActual
end