import LeanFormal.IUT.Audit.Status

/-! # S3164: GenEll P0 re-audit (fixed 06/07/08 + pending 05)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- P0 re-audit rows (file, checker, decls, src bytes, sha256 prefix, note). -/
def S3164GenEllP0Reaudit : List (String × String × Nat × Nat × String × String) := [
  ("GenEll06Section3StatementsActual.lean", "CITABLE", 3, 4481, "34921AD1BBD651D04C4FAC60DD14AF45B874784F47F0AF8391EBBD1F08DB2997", "section-3 statement rows (9 rows, decide length); recursion fix applied"),
  ("GenEll07Section4StatementsActual.lean", "CITABLE", 3, 3741, "62C02C0B3A9881CC72B221EA956D88EB63B781635B706FE953320F138B891144", "section-4 statement rows (5 rows, decide length); recursion fix applied"),
  ("GenEll08MainReductionActual.lean", "CITABLE", 5, 2423, "073E147F5076F36F0541C0C73215B766E360A05F67AE6E1C4D0D4AC34DD0F1FF", "main reduction shape + IUT IV section-2 consumer + 4 citations"),
  ("GenEll05Theorem21Actual.lean", "PENDING (regressed EXIT=1, being fixed)", 8, 3759, "-", "was CITABLE at 3037B; extension in progress"),
  ("GenEll04bProp17ChainActual.lean", "PENDING", 4, 2323, "-", "queued/compiling") ]

theorem S3164GenEllP0Reaudit_length : S3164GenEllP0Reaudit.length = 5 := rfl

/-- P0 re-audit record. -/
def S3164GenEllP0ReauditRecord : Obligation :=
  { id := "IUT.project.genell-p0-reaudit"
    source := "checker scan 2026-11-10 05:40"
    status := VerificationStatus.interface
    note :=
      "GENELL P0 RE-AUDIT: GenEll06/07/08 now CITABLE after the recursion fix (statement-row lists "
      ++ "with decide lengths; main reduction shape + consumer); GenEll05 regressed during "
      ++ "extension (EXIT=1, old CITABLE version 3037B superseded) and GenEll04b pending. GenEll06 "
      ++ "/07 are statement ledgers (paper-fidelity rows) — still need paper-specific instantiation "
      ++ "tracking per Lead note."
    dependsOn := [ "S3163GenEllAuditProtocolRecord" ] }

#check S3164GenEllP0ReauditRecord
#check S3164GenEllP0Reaudit_length

end LeanFormal.IUT.Audit
