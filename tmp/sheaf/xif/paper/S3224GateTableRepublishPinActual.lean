import LeanFormal.IUT.Audit.Status

/-! # S3224: CANONICAL GATE TABLE REPUBLISHED (IUTExternal34GateV75) — pin verified

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Gate table pin rows. -/
def S3224GateTablePin : List (String × String × String) := [
  ("canonical path", "PIN", "tmp/sheaf/xif/paper/IUTExternal34GateV75Actual.lean (retired: IUTExternal33GateV37Actual corrupt; IUTExternal34GateV38 duplicate non-canonical)"),
  ("file", "PIN", "EXIT=0 SIZE 11816B; src sha 105A0336EDDB5512...; checker WITH IUTExternal34GateProbe: CITABLE 2 decls, olean_fresh true, last_exit 0, probe_ok TRUE"),
  ("olean", "PIN", "olean 252808 sha 66224742BDA349A2..."),
  ("rows", "VERBATIM", "(a) 2.4 row COMPLETE interface level with FINAL VERDICT S3223 (17 evidence files; named global remaining); (b) S3178 row GREEN/CITABLE EXIT0 SIZE 20411B; (c) GChoiceIntegration row TEMP-REGRESSED (disk 10023B EXIT=1; not recorded)"),
  ("verdict", "CANONICAL GATE PIN VERIFIED", "clean republish verified fresh/citable/probe_ok; rows compact <1800 chars; pins 14041/23066/18800; no registry edits") ]

theorem S3224GateTablePin_length : S3224GateTablePin.length = 5 := rfl

/-- Record. -/
def S3224GateTablePinRecord : Obligation :=
  { id := "IUT.project.canonical-gate-table-v75-pin"
    source := "lattice republish 2026-11-10 19:35; checker+probe audit"
    status := VerificationStatus.interface
    note :=
      "CANONICAL GATE TABLE REPUBLISHED (IUTExternal34GateV75Actual): EXIT=0 SIZE 11816B, src "
      ++ "sha 105A0336..., olean 252808 66224742...; checker WITH IUTExternal34GateProbe: CITABLE "
      ++ "2 decls, olean_fresh true, last_exit 0, probe_ok TRUE. Rows: 2.4 COMPLETE interface "
      ++ "level (S3223 verdict + named remaining); S3178 GREEN 20411B; GChoiceIntegration TEMP-"
      ++ "REGRESSED. Old IUTExternal33GateV37 retired corrupt; V38 duplicate non-canonical."
    dependsOn := [ "S3223Lemma24VerdictRecord" ] }

#check S3224GateTablePinRecord
#check S3224GateTablePin_length

end LeanFormal.IUT.Audit
