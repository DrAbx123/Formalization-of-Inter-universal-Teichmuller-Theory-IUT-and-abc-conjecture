import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual

/-! # Actual q-pilot link identification -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.OriginalInput.ThetaLinkQPilotActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual q-pilot link identification at the source (1,0) strip. -/
noncomputable def actualQPilotLinkIdentification :
    QPilotLinkIdentification I I.qPilotStripAtOneZero where
  qPilotStrip_eq := rfl
  qPilotLogVolume := I.qPilotSignedLogVolume
  qPilotLogVolume_eq := rfl

theorem actualQPilotLinkIdentification_qPilotLogVolume :
    (actualQPilotLinkIdentification I).qPilotLogVolume =
      I.qPilotSignedLogVolume := rfl

end LeanFormal.IUT.Theorem311Source.OriginalInput.ThetaLinkQPilotActual

end
