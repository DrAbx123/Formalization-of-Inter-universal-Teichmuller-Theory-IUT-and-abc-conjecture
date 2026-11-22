import LeanFormal.IUT.Audit.Status

/-! # S3163: GenEll batch audit protocol (shehdd checker/audit/watch)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- GenEll batch audit steps (kernel-ci). -/
def S3163GenEllAuditProtocol : List String := [
  "STEP 0: run tools/xif_deep_search.ps1 -Query '<exact type/lemma names>' and read coord/PRIOR-ART-INDEX.md sections A-F; batch report first line = 'STEP 0 prior-art: <queries> -> <hits> -> reuse|adapt|none'; append new precedents to PRIOR-ART-INDEX",
  "verify each batch file: results.log last line EXIT=0 + olean fresh + ACTUAL declarations (theorem/def/structure; no doc-only) + declaration list names match the batch report",
  "run tools/xif_citable_check.ps1 -File <f> -Probe <probe> => verdict CITABLE (olean_fresh, last_exit 0, declarations, probe_ok)",
  "kernel probe: all cited declarations trio-only [propext, Classical.choice, Quot.sound] or no-axiom; ZERO sorryAx; report any changed footprint",
  "fidelity: compare statements vs corpus lines (GenEll §1 99-604 / §2 606-687 / §3 738-1199 / §4 1200-1425); paper-proved-but-not-formalized results registered as precisely named paper-input theorems (corpus line numbers + status), never as fake proofs",
  "reuse check: no re-proving of existing assets (BD class tools, GenEll shapes, height/weight layer, shadow adapter); no vendor imports (separate lake, explain instead)",
  "record to appendices: append audit row (file, size, sha256, olean sha, checker verdict, decl count, probe status) to coord/GENELL-AUDIT-APPENDIX.md + ledger",
  "registry status: FROZEN at 14041; NO reopen/re-pin during GenEll work; only a paper-level milestone may consider one update" ]

theorem S3163GenEllAuditProtocol_length : S3163GenEllAuditProtocol.length = 8 := rfl

/-- GenEll audit protocol record. -/
def S3163GenEllAuditProtocolRecord : Obligation :=
  { id := "IUT.project.genell-audit-protocol"
    source := "Lead GenEll task; coord/GENELL-FORMALIZATION-PLAN.md §3 (shehdd checker/audit/watch)"
    status := VerificationStatus.interface
    note :=
      "GENELL AUDIT PROTOCOL: per batch verify EXIT=0 + fresh olean + real declarations + checker "
      ++ "CITABLE with probe + trio/no-sorry footprints; compare statements against corpus lines; "
      ++ "register paper-proved-but-unformalized results as named paper-input theorems; record "
      ++ "audit rows to coord/GENELL-AUDIT-APPENDIX.md + ledger; registry FROZEN 14041."
    dependsOn := [ "S3162Step0DeepSearchRecord" ] }

#check S3163GenEllAuditProtocolRecord
#check S3163GenEllAuditProtocol_length

end LeanFormal.IUT.Audit
