import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import tmp.sheaf.xif.paper.Mzk1ABCEntryQpilotActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected Gap2 object-level calibration

Bridge calibration (NOT a Gap2 shape equivalence): the nonemptiness of the bridge object is
equivalent to ABCConjecture (green `paperGap_boundary_calibrated`). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap2IffABCACtual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual

theorem bridge_nonempty_iff_ABC :
    Nonempty Cor312ToABCBridgeInterface ↔ ABCConjecture :=
  Mzk1FinalBoundaryCertificateV2Actual.v2_calibrated

theorem bridge_to_ABC (D : Cor312ToABCBridgeInterface) : ABCConjecture :=
  abcEntry_abcConjecture D

theorem bridge_nonempty_iff_ABC' :
    (Nonempty Cor312ToABCBridgeInterface) ↔ ABCConjecture :=
  corrected_gap2_iff_ABC

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap2IffABCACtual

end
