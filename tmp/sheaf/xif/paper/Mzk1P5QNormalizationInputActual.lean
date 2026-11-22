import tmp.sheaf.xif.paper.Mzk1P5BridgeIntegrationActual
import tmp.sheaf.xif.paper.Mzk1P5LabelShiftActual
import tmp.sheaf.xif.paper.Mzk1P5BridgeInstantiateActual

/-!
# P5: packaged q-normalization input and conditional bridge comparison

This file packages the remaining P5 named inputs into one structure
P5QNormalizationInput and derives p5_bridge_compare from it.

The structure data is exactly a P5AnalyticRootBridge, so it contains:
* root_image : toRoot r = (qRoot)^l  (the corrected root choice);
* the mu2l phase family phase_j with phase_pow;
* c_j and the comparison field (the CJ-L form).

It does NOT construct the analytic-to-root map, the phase family, or the
Kummer/line-bundle comparison.  Those are the actual sources still missing;
see coord/ROUTE3-CTHETA.md section 8.12.
-/

-- retrigger after label-shift open
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5QNormalizationInputActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
open LeanFormal.IUT.Foundations.Theta

universe u v

/-- The packaged q-normalization data.  It is a wrapper around the bridge so
that all named inputs (root choice, phase, c_j, comparison) are one object. -/
structure P5QNormalizationInput (L : Type u) (R : Type v) [Field L] [Field R]
    (l : PrimeGeFive) where
  data : P5AnalyticRootBridge L R l

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {R : Type v} [Field R] {l : PrimeGeFive}
variable (I : P5QNormalizationInput L R l)

/-- p5_bridge_compare follows directly from the packaged input. -/
theorem p5_bridge_compare_of_qNormalizationInput
    (q i : L) (hr : I.data.r ^ 2 = q) (hr0 : I.data.r ≠ 0)
    (hi : i ^ 2 = -1) (hq : ‖q‖ < 1) (hTheta : oddTheta q i ≠ 0)
    (j : ThetaLabel (l := l)) :
    I.data.toRoot (oddTheta q (Mzk1P5LabelShiftActual.analyticThetaLabelPoint i I.data.r j) / oddTheta q i) =
      (I.data.c j : R) * (I.data.phase j : R) * (I.data.thetaUnit j : R) := by
  exact p5_bridge_compare (B := I.data) q i hr hr0 hi hq hTheta j

#print axioms p5_bridge_compare_of_qNormalizationInput

end LeanFormal.IUT.XiFPaper.Mzk1P5QNormalizationInputActual
