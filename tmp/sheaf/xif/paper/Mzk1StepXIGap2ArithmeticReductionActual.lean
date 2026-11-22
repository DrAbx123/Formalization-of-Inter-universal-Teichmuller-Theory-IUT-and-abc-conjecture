import tmp.sheaf.xif.paper.Mzk1StepXIGap2ShapeDecompositionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap2 arithmetic reduction

Reduction to the explicit summand form `(1+eps)*weight + (theta + D)`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ArithmeticReductionActual

open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ShapeDecompositionActual

theorem gap2_reduction_ennreal (S : Gap2Shape) :
    S.regionVolume ≤ ENNReal.ofReal ((1 + S.eps) * S.weight + (S.theta + S.D)) := by
  have h := S.named
  rw [show (1 + S.eps) * S.weight + S.theta + S.D =
      (1 + S.eps) * S.weight + (S.theta + S.D) by ring] at h
  exact h

theorem gap2_reduction_real (S : Gap2Shape)
    (hR : 0 ≤ (1 + S.eps) * S.weight + (S.theta + S.D)) :
    S.regionVolume.toReal ≤ (1 + S.eps) * S.weight + (S.theta + S.D) :=
  gap2_real_bound hR (gap2_reduction_ennreal S)

theorem gap2_reduction_sum_eq (S : Gap2Shape) :
    (1 + S.eps) * S.weight + S.theta + S.D =
      (1 + S.eps) * S.weight + (S.theta + S.D) := by ring

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ArithmeticReductionActual

end
