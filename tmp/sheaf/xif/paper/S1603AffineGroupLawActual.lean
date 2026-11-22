import tmp.sheaf.xif.paper.S1601ZSMulPointFormulaActual
import tmp.sheaf.xif.paper.S1593ZSMulFieldActual
import tmp.sheaf.xif.paper.S1598PolyToFieldCCActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual

/-- The actual tangent slope at the universal point (X,Y). -/
noncomputable def slopeOne : Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

/-- First missing affine lemma: the gap between smulY n and negY. -/
def S1603SmulYSubNegY : Prop :=
  forall n : Int, n ≠ 0 ->
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) =
      ψᵤ (2 * n) / (ψᵤ n) ^ 4

/-- Nonvanishing of the gap. -/
def S1603SmulYNeNegY : Prop :=
  forall n : Int, n ≠ 0 ->
    smulY n ≠ pointedCurve.toAffine.negY (smulX n) (smulY n)

/-- Closed form of the tangent slope. -/
def S1603SlopeOneEq : Prop :=
  slopeOne = -polyToField curve.toAffine.polynomialX / ψᵤ 2

/-- Doubling X-coordinate, tangent branch. -/
def S1603AddXSmulOne : Prop :=
  pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2

/-- Doubling Y-coordinate, tangent branch. -/
def S1603AddYSmulOne : Prop :=
  pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2

/-- Chord X formula. -/
def S1603SmulXAdd : Prop :=
  forall m n : Int, m ≠ 0 -> n ≠ 0 -> n + m ≠ 0 -> n - m ≠ 0 ->
    smulX (n + m) = smulX (n - m) -
      (smulY (n) - pointedCurve.toAffine.negY (smulX n) (smulY n)) *
      (smulY m - pointedCurve.toAffine.negY (smulX m) (smulY m)) /
        (smulX m - smulX n) ^ 2

end LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
end