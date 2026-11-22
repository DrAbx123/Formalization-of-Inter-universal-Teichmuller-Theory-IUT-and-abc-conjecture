import tmp.sheaf.xif.paper.S1611PolynomialXRearrangeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1612ZSMulPointFinalActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open LeanFormal.IUT.XiFPaper.S1611PolynomialXRearrangeActual

/-- Tangent doubling X. -/
def S1612AddXSmulOne : Prop :=
  pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2

/-- Tangent doubling Y. -/
def S1612AddYSmulOne : Prop :=
  pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2

/-- Chord X. -/
def S1612SmulXAdd : Prop :=
  forall m n : Int, m ≠ 0 -> n ≠ 0 -> n + m ≠ 0 -> n - m ≠ 0 ->
    smulX (n + m) = smulX (n - m) -
      (smulY n - Affine.negY pointedCurve.toAffine (smulX n) (smulY n)) *
      (smulY m - Affine.negY pointedCurve.toAffine (smulX m) (smulY m)) /
        (smulX m - smulX n) ^ 2

/-- Chord Y. -/
def S1612SmulYAddSubNegY : Prop :=
  forall m n : Int, m ≠ 0 -> n ≠ 0 -> n + m ≠ 0 -> n - m ≠ 0 ->
    smulY (n + m) - Affine.negY pointedCurve.toAffine (smulX (n + m)) (smulY (n + m)) =
      ((smulY m - Affine.negY pointedCurve.toAffine (smulX m) (smulY m)) *
        (smulX n - smulX (n + m)) -
       (smulY n - Affine.negY pointedCurve.toAffine (smulX n) (smulY n)) *
        (smulX m - smulX (n + m))) / (smulX m - smulX n)

end LeanFormal.IUT.XiFPaper.S1612ZSMulPointFinalActual
end