import tmp.sheaf.xif.paper.S1607SlopeOneEqActual
import tmp.sheaf.xif.paper.S1596UniversalAffineZSMulActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1608SlopeOneEqExplicitActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open LeanFormal.IUT.XiFPaper.S1607SlopeOneEqActual

/-- polyToField (C X) = smulX 1. -/
theorem s1608_polyToField_CX :
    polyToField (C Polynomial.X) = smulX 1 := by
  rw [← smulX_one]

/-- polyToField Y = smulY 1. -/
theorem s1608_polyToField_X :
    polyToField Polynomial.X = smulY 1 := by
  rw [← smulY_one]

/-- polyToField (C (C a)) = algebraMap a. -/
theorem s1608_polyToField_CC (a : MvPolynomial Coeff ℤ) :
    polyToField (C (C a)) = algebraMap (MvPolynomial Coeff ℤ) Field a := by
  simpa [CC] using s1598PolyToField_CC a

/-- Exact slope target after the three unification lemmas. -/
def S1608SlopeOneEq : Prop :=
  slopeOne = -polyToField curve.toAffine.polynomialX / ψᵤ 2

end LeanFormal.IUT.XiFPaper.S1608SlopeOneEqExplicitActual
end