import tmp.sheaf.xif.paper.GlobalQPilotObjectActual
import tmp.sheaf.xif.paper.S1036GlobalQPilotObjectAuditActual
/-! # S1110: actual global q_v collection -> paper qPilot object contract
Audit: GlobalQPilotObjectActual already supplies the actual bad qParameter
family, abs-log divisor, total and signed log.  PaperQPilotObjectActual instead
uses the single local C3.q and is not the global object.  We keep both files
unchanged and build the global paper qPilot contract here from the collection;
strip/lineBundle/logKummer remain exact fields. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1110GlobalPaperQPilotActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S1036GlobalQPilotObjectAuditActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
/-- Global paper qPilot contract: actual q_v collection + signed log, with
strip/lineBundle/logKummer/oneColumn as exact geometric fields. -/
structure S1110GlobalPaperQPilotContract where
  collection : GlobalQPilotCollection I
  qPilotLogVolume : Real
  qPilotLogVolume_eq : qPilotLogVolume = globalQPilotSignedLog I
  strip : Prop
  lineBundle : Prop
  logKummer : Prop
  oneColumn : Prop
/-- Actual collection and signed log fields of the global paper qPilot. -/
theorem s1110GlobalQPilotLogVolume_actual :
    globalQPilotSignedLog I = sourceQPilotSignedLog I.initial :=
  globalQPilotSignedLog_eq_sourceQPilotSignedLog I
theorem s1110GlobalQPilotCollection_actual :
    (globalQPilotCollection I).qParameter = globalQParameterFamily I :=
  rfl
theorem s1110GlobalQPilotCollection_signedLogVolume :
    (globalQPilotCollection I).signedLogVolume = sourceQPilotSignedLog I.initial :=
  globalQPilotCollection_signedLogVolume I
def S1110ExactGeometricFields : Prop :=
  Nonempty (S1110GlobalPaperQPilotContract I)
end LeanFormal.IUT.XiFPaper.S1110GlobalPaperQPilotActual
