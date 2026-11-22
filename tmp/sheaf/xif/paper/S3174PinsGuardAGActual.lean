import LeanFormal.IUT.Audit.Status

/-! # S3174: pins guard AG (frozen 14041)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Pins guard string. -/
def S3174PinsGuard : String := "gate=23066|registry=14041|record=18800|reopens=3|phase=ETTH_THM38_AUDIT|registry_frozen=14041|repin=none"

theorem S3174PinsGuard_eq :
    S3174PinsGuard =
      "gate=23066|registry=14041|record=18800|reopens=3|phase=ETTH_THM38_AUDIT|registry_frozen=14041|repin=none" := rfl

/-- Pins guard AG record. -/
def S3174PinsGuardAG : Obligation :=
  { id := "IUT.project.pins-guard-ag"
    source := "batch AG 2026-11-10 06:17"
    status := VerificationStatus.interface
    note := "PINS: registry FROZEN 14041 / gate 23066 / record 18800; no reopen/re-pin."
    dependsOn := [ "S3173PinsGuardAF", "S3174EtThBatchAuditRecord" ] }

#check S3174PinsGuardAG
#check S3174PinsGuard_eq

end LeanFormal.IUT.Audit
