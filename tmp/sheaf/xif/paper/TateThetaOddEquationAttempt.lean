import tmp.sheaf.xif.paper.TateThetaLogDerivAttempt
import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation

noncomputable section
open LeanFormal.IUT.TateCurve
open LeanFormal.IUT.XiFPaper.TateThetaLogDerivAttempt
open WeierstrassCurve
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateThetaOddEquationAttempt

universe u

variable {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]

/-- Minimal odd-coordinate identity target. -/
def TateThetaOddIdentityTarget (q u : K) : Prop :=
  inversionOddYCoordinateSeries q u ^ 2 =
    4 * coordinateSeries q u ^ 3 + coordinateSeries q u ^ 2 +
      4 * a4 K q * coordinateSeries q u + 4 * a6 K q

/-- The same identity written with the formal theta log derivatives. -/
def TateThetaLogDerivOddTarget (q u : K) : Prop :=
  thetaLogDeriv3 q u ^ 2 =
    4 * thetaLogDeriv2 q u ^ 3 + thetaLogDeriv2 q u ^ 2 +
      4 * a4 K q * thetaLogDeriv2 q u + 4 * a6 K q

theorem TateThetaLogDerivOddTarget_iff_oddIdentity (q u : K) :
    TateThetaLogDerivOddTarget q u ↔ TateThetaOddIdentityTarget q u := by
  unfold TateThetaLogDerivOddTarget TateThetaOddIdentityTarget
  rw [thetaLogDeriv2_eq_coordinateSeries,
    thetaLogDeriv3_eq_inversionOddYCoordinateSeries]

theorem TateThetaOddIdentityTarget_iff_tateWeierstrassEquation
    (q u : K) (hq : ‖q‖ < 1) :
    TateThetaOddIdentityTarget q u ↔ tateWeierstrassEquation q u := by
  unfold TateThetaOddIdentityTarget
  exact (tateWeierstrassEquation_iff_oddSeries hq u).symm

#check WeierstrassCurve.Affine.Equation
#check WeierstrassCurve.Affine.equation_iff
#check WeierstrassCurve.Affine.Nonsingular
#check WeierstrassCurve.Affine.addX
#check WeierstrassCurve.Affine.addY
#check WeierstrassCurve.Affine.slope
#check WeierstrassCurve.Affine.negY
#check TateThetaOddIdentityTarget
#check TateThetaLogDerivOddTarget
#check TateThetaOddIdentityTarget_iff_tateWeierstrassEquation
#print axioms TateThetaOddIdentityTarget_iff_tateWeierstrassEquation

end LeanFormal.IUT.XiFPaper.TateThetaOddEquationAttempt
end