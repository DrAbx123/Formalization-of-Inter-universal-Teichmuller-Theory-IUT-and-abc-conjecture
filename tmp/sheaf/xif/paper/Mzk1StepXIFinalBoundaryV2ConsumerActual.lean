import tmp.sheaf.xif.paper.Mzk1StepXIGap2ABCStrengthActual
import tmp.sheaf.xif.paper.Mzk1StepXIGap2ArithmeticActual
import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi FinalBoundary V2 consumer

V2 boundary consumer: Gap2 arithmetic + ABC strength + canonical certificate gate. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalBoundaryV2ConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ABCStrengthActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ArithmeticActual

theorem final_boundary_v2_ABC :
    Nonempty Cor312ToABCBridgeInterface ↔ ABCConjecture :=
  gap2_strength_iff_ABC

theorem final_boundary_v2_arithmetic (S : Gap2Shape)
    (hR : 0 ≤ (1 + S.eps) * S.weight + S.theta + S.D) :
    S.regionVolume.toReal - (1 + S.eps) * S.weight ≤ S.theta + S.D :=
  gap2_arithmetic_real S hR

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateActual.finalBoundaryCertificate

end LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalBoundaryV2ConsumerActual

end
