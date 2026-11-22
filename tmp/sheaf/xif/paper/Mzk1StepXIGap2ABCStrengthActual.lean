import tmp.sheaf.xif.paper.Mzk1StepXICorrectedGap2IffABCACtual
import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap2 strength relation to ABC

Read-only relation: Gap2 bridge object nonemptiness is equivalent to ABC, and the
final boundary certificate remains the canonical consumer. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ABCStrengthActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap2IffABCACtual

theorem gap2_strength_iff_ABC :
    Nonempty Cor312ToABCBridgeInterface ↔ ABCConjecture :=
  corrected_gap2_iff_ABC

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateActual.finalBoundaryCertificate
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap2IffABCACtual.corrected_gap2_iff_ABC

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ABCStrengthActual

end
