import tmp.sheaf.xif.paper.Mzk1StepXIGap2ShapeDecompositionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap2 arithmetic chain

End-to-end chain from the named estimate to the real arithmetic inequality. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ArithmeticChainActual

open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ShapeDecompositionActual

theorem gap2_chain (S : Gap2Shape)
    (hR : 0 ≤ (1 + S.eps) * S.weight + S.theta + S.D) :
    S.regionVolume.toReal - (1 + S.eps) * S.weight ≤ S.theta + S.D :=
  by linarith [gap2_shape_real S hR]

theorem gap2_chain_nonneg (S : Gap2Shape)
    (hR : 0 ≤ (1 + S.eps) * S.weight + S.theta + S.D) :
    0 ≤ S.theta + S.D + (1 + S.eps) * S.weight - S.regionVolume.toReal := by
  have h := gap2_chain S hR
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ArithmeticChainActual

end
