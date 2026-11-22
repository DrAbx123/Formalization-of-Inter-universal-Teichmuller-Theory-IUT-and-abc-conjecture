import LeanFormal.IUT.Audit.Status

/-! # S3184: pins guard AN (frozen 14041)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Pins guard string. -/
def S3184PinsGuard : String := "gate=23066|registry=14041|record=18800|reopens=3|phase=S3180_FINAL_PIN|registry_frozen=14041|repin=none"

theorem S3184PinsGuard_eq :
    S3184PinsGuard =
      "gate=23066|registry=14041|record=18800|reopens=3|phase=S3180_FINAL_PIN|registry_frozen=14041|repin=none" := rfl

/-- Pins guard AN record. -/
def S3184PinsGuardAN : Obligation :=
  { id := "IUT.project.pins-guard-an"
    source := "final pin audit 2026-11-10 08:11"
    status := VerificationStatus.interface
    note := "PINS: registry FROZEN 14041 / gate 23066 / record 18800; no reopen/re-pin."
    dependsOn := [ "S3183PinsGuardAM", "S3184S3180FinalPinRecord" ] }

#check S3184PinsGuardAN
#check S3184PinsGuard_eq

end LeanFormal.IUT.Audit
