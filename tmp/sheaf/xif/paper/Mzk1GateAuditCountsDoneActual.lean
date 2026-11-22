/- Counts/contents of the gate audit lists (accepted / revoked / open). -/
import tmp.sheaf.xif.paper.GateAuditCurrentActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GateAuditCountsDoneActual
open LeanFormal.IUT.XiFPaper.GateAuditCurrentActual
theorem gateAccepted_len : gateAuditAccepted.length = 14 := rfl
theorem gateRevoked_len : gateAuditRevoked.length = 5 := rfl
theorem gateOpen_len : gateAuditOpenBlockers.length = 5 := rfl
theorem gateAccepted_nonempty : gateAuditAccepted.length > 0 := by decide
#print axioms gateAccepted_len
end LeanFormal.IUT.XiFPaper.Mzk1GateAuditCountsDoneActual
end
