import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.PaperQPilotLogVolume
/-! # S630: actual PaperQPilotObjectActual versus PaperXiFSourceLink
The actual object has signedQPilotLogVolume = localSignedLog C3.q, and paperQPilotLogVolume C3 has the same definition; their equality is rfl.  The legacy PaperXiFSourceLink is typed on old PaperQPilotObject with Real qPilotLogVolume = sourceQPilotSignedLog I.initial, so it cannot be filled directly; the exact bridge/source-q identification is recorded. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S630ActualQPilotXiFLinkAudit
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper
universe ua uv upi umon ui uC3 uD3
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (P : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I))
/-- On the actual carrier, signed q-pilot log is definitionally the paper scalar. -/
theorem actual_signedQPilotLogVolume_eq_paper :
    P.signedQPilotLogVolume = paperQPilotLogVolume P.line.C3 := rfl
/-- The WithTop version is also definitional. -/
theorem actual_qPilotLogVolume_eq_paper_withTop :
    P.line.qPilotLogVolume = (paperQPilotLogVolume P.line.C3 : WithTop Real) := by
  rw [P.line.qPilotLogVolume_eq_signed]
  rfl
/-- Exact source-q identification needed to compare the actual signed scalar
with the legacy Real scalar sourceQPilotSignedLog I.initial. -/
def ActualToLegacySourceQIdentification : Prop :=
  sourceQPilotSignedLog I.initial = P.signedQPilotLogVolume
/-- The legacy PaperXiFSourceLink cannot be constructed directly from the
actual carrier: it needs the old PaperQPilotObject plus this bridge and the
paper link fields.  The minimal exact data are recorded here. -/
structure ActualPaperXiFLinkBridge where
  source_q_identification : ActualToLegacySourceQIdentification (I := I) P
  source_identifications_required : Prop
  link_identification : Prop
  link_implies_inclusion : Prop
def ActualPaperXiFLinkBridgeRequired : Prop :=
  Nonempty (ActualPaperXiFLinkBridge (I := I) P)
end LeanFormal.IUT.XiFPaper.S630ActualQPilotXiFLinkAudit
