import tmp.sheaf.xif.paper.Mzk1P5LabelShiftActual
import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual

/-!
# CONDITIONAL (named structure): P5 analytic/root bridge integration

This file packages the named bridge inputs into P5AnalyticRootBridge and proves
the conditional comparison with the abstract root-unit layer.  The structure
carries the target root field R, the analytic-to-root ring map, the constants
c_j, the phases phase_j, and the root-unit family thetaUnit.  All are explicit
input data; none is constructed here.

The actual paperRootThetaUnit instantiation is the intended instance of the
thetaUnit field; the exact GAP between thetaUnit and paperRootThetaUnit is
recorded in coord/ROUTE3-CTHETA.md.  No toy field or fake bridge is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.Foundations.Theta

universe u v

/-- Named bridge data: L analytic field, R target root field, l the paper
label parameter. -/
structure P5AnalyticRootBridge (L : Type u) [Field L] (R : Type v) [Field R]
    (l : PrimeGeFive) where
  toRoot : L →+* R
  r : L
  qRoot : Rˣ
  root_image : toRoot r = (qRoot : R) ^ l.value
  thetaUnit : ThetaLabel (l := l) → Rˣ
  c : ThetaLabel (l := l) → Rˣ
  phase : ThetaLabel (l := l) → Rˣ
  phase_pow : ∀ j, phase j ^ (2 * l.value) = 1
  comparison : ∀ j : ThetaLabel (l := l),
    toRoot (r ^ (-(thetaLabelExponent (l := l) j ^ 2))) =
      (c j : R) * (phase j : R) * (thetaUnit j : R)

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {R : Type v} [Field R] {l : PrimeGeFive}
variable (B : P5AnalyticRootBridge L R l)

/-- Conditional comparison: the analytic normalized ratio maps to the root
unit with explicit constants c_j and phases phase_j. -/
theorem p5_bridge_compare
    (q i : L) (hr : B.r ^ 2 = q) (hr0 : B.r ≠ 0) (hi : i ^ 2 = -1)
    (hq : ‖q‖ < 1) (hTheta : oddTheta q i ≠ 0)
    (j : ThetaLabel (l := l)) :
    B.toRoot (oddTheta q (analyticThetaLabelPoint i B.r j) / oddTheta q i) =
      (B.c j : R) * (B.phase j : R) * (B.thetaUnit j : R) := by
  rw [oddThetaFraction_eval_thetaLabel q B.r i hr hr0 hi hq hTheta j]
  exact B.comparison j



#print axioms p5_bridge_compare

end LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
