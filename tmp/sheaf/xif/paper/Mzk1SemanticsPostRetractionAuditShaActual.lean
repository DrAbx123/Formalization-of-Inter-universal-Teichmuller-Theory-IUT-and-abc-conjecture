import Mathlib.Tactic

/-!
# A712 semantics post-retraction audit (Sha, table rows only)

Audit of the A703/A704 retraction state across the shehdd V2/semantics tables:
* the four tables (`FinalSemantics`, `FinalBoundaryCertificateV2`, `OneWayTightness`,
  `B1B2Status`) carry RETRACTED rows for the hfull/N-scaling chain and N1 new-route rows;
* no shehdd file cites `final_conditional_ABC` / `final_theorem_package` /
  `natRadicalWeightBound_iff_ABC` as a conclusion (only retraction notices/vacuity proof);
* machine proof of vacuity: `Mzk1FinalConditionalVacuityShaActual.hfull_unsatisfiable`
  (compiled, axioms trio);
* new work uses triple-dependent Theta-data: bad primes = primes(abc), q=(abc)^2,
  normalized weight [F_v:Q_p]/[F:Q]; the N1 model itself is the abc lane task;
* canonical old files remain mainline responsibility for their own RETRACTED marking.

This file is an audit table only.  No sorry/axiom/True.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1SemanticsPostRetractionAuditShaActual

structure AuditRow where
  target : String
  content : String
  status : String
  deriving Repr, DecidableEq

def auditRows : List AuditRow :=
  [ ⟨"Mzk1FinalSemanticsShaActual", "RETRACTED rows for hfull chain; NEW_ROUTE_NAMED N1 row; no vacuous conclusion", "AUDITED"⟩
  , ⟨"Mzk1FinalBoundaryCertificateV2ShaActual", "RETRACTED rows; N1 route row; retracted #print gates removed", "AUDITED"⟩
  , ⟨"Mzk1OneWayTightnessShaActual", "legacy direction RETRACTED; N1 route; converse NOT_PROVED", "AUDITED"⟩
  , ⟨"Mzk1B1B2StatusShaActual", "legacy N-scaling Gap2 RETRACTED; N1 route; no NAMED in old frame", "AUDITED"⟩
  , ⟨"vacuous conclusions grep", "final_conditional_ABC / final_theorem_package / natRadicalWeightBound_iff_ABC appear only in retraction notices", "AUDITED"⟩
  , ⟨"vacuity machine proof", "Mzk1FinalConditionalVacuityShaActual.hfull_unsatisfiable (axioms trio)", "GREEN"⟩
  , ⟨"new route N1", "triple-dependent Theta-data; bad=primes(abc); q=(abc)^2; normalized weight; PENDING_ABC_LANE", "NEW_ROUTE_NAMED"⟩
  , ⟨"canonical old files", "mainline responsibility; shehdd did not modify", "NOTE"⟩
  , ⟨"scope", "audit only; no conclusion claimed", "INTEGRITY"⟩
  ]

theorem auditRows_length : auditRows.length = 9 := rfl

theorem auditRows_statuses_ok :
    auditRows.all (fun r =>
      r.status ∈ ["AUDITED", "GREEN", "NEW_ROUTE_NAMED", "NOTE", "INTEGRITY"]) = true := by
  decide

theorem audit_has_vacuity_proof :
    auditRows.any (fun r => r.status = "GREEN") = true := by
  decide

theorem audit_has_n1_route :
    auditRows.any (fun r => r.status = "NEW_ROUTE_NAMED") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1SemanticsPostRetractionAuditShaActual
