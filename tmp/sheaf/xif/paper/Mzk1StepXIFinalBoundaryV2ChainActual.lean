import tmp.sheaf.xif.paper.Mzk1StepXIGap2ABCStrengthActual
import tmp.sheaf.xif.paper.Mzk1StepXIGap2ArithmeticChainActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi FinalBoundary V2 chain

Final boundary V2 chain: Gap2 arithmetic and ABC strength in one consumer. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalBoundaryV2ChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ABCStrengthActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ShapeDecompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ArithmeticChainActual

theorem finalV2_chain_ABC :
    Nonempty Cor312ToABCBridgeInterface ↔ ABCConjecture :=
  gap2_strength_iff_ABC

theorem finalV2_chain_arithmetic (S : Gap2Shape)
    (hR : 0 ≤ (1 + S.eps) * S.weight + S.theta + S.D) :
    S.regionVolume.toReal - (1 + S.eps) * S.weight ≤ S.theta + S.D :=
  gap2_chain S hR

end LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalBoundaryV2ChainActual

end
