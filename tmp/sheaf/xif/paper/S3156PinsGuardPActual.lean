import LeanFormal.IUT.Audit.Status

/-! # S3156: pins guard P (repo-first corrective phase; no reopen)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Pins guard string. -/
def S3156PinsGuard : String := "gate=23066|registry=13129|record=15501|reopens=2|phase=REPO_FIRST_CORRECTIVE|third_reopen=WAITING|repin=none"

theorem S3156PinsGuard_eq :
    S3156PinsGuard =
      "gate=23066|registry=13129|record=15501|reopens=2|phase=REPO_FIRST_CORRECTIVE|third_reopen=WAITING|repin=none" := rfl

/-- Pins guard P record. -/
def S3156PinsGuardP : Obligation :=
  { id := "IUT.project.pins-guard-p"
    source := "Lead §7.9 repo-first corrective phase"
    status := VerificationStatus.interface
    note :=
      "PINS LOCKED: gate 23066 / registry 13129 / record 15501; 2 reopens consumed; repo-first "
      ++ "corrective phase for model-route files; third reopen WAITING; no re-pin."
    dependsOn := [ "S3155PinsGuardO" ] }

#check S3156PinsGuardP
#check S3156PinsGuard_eq

end LeanFormal.IUT.Audit
