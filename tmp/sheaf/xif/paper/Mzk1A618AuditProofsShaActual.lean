import tmp.sheaf.xif.paper.Mzk1A618AuditMachineShaActual

/-!
# shehdd A625 A618 audit proofs (separate file, Sha)

Separate the machine-checked audit PROOFS from the data table: thin aliases of the
`decide` proofs in `Mzk1A618AuditMachineShaActual`.  Kept in its own file/namespace
so the data table can change without touching the proof surface.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1A618AuditProofsShaActual

open LeanFormal.IUT.XiFPaper.Mzk1A618AuditMachineShaActual

theorem audit_length_proof : auditRows.length = 13 :=
  auditRows_length

theorem audit_statuses_proof :
    auditRows.all (fun r => r.status ∈ allowedStatuses) = true :=
  auditRows_allowed

theorem audit_gap1_present :
    auditRows.any (fun r => r.name = "Gap1 height estimate") = true :=
  audit_has_gap1

theorem audit_gap2_present :
    auditRows.any (fun r => r.name = "Gap2 volume estimate") = true :=
  audit_has_gap2

theorem audit_triple_scaling_present :
    auditRows.any (fun r => r.name = "triple-dependent scaling design") = true :=
  audit_has_triple_scaling

theorem audit_canonical_bridge_green :
    auditRows.any (fun r => r.name = "canonical mainline S1902 bridge" ∧ r.status = "GREEN") = true :=
  audit_has_canonical_bridge_green

theorem audit_counterexample_present :
    auditRows.any (fun r => r.name = "3+125=128 height>weight counterexample") = true :=
  audit_has_counterexample

end LeanFormal.IUT.XiFPaper.Mzk1A618AuditProofsShaActual
