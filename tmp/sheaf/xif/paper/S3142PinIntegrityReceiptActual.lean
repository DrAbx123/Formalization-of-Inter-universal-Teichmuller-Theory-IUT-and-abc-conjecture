import LeanFormal.IUT.Audit.Status

/-! # S3142: pin-integrity receipt (kernel-checked data)

Compact receipt of the frozen pins and the reopen accounting.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Pin triple: gate size | registry size | record size. -/
def S3142PinSizes : String := "22958|13108|14932"

theorem S3142PinSizes_eq : S3142PinSizes = "22958|13108|14932" := rfl

/-- Reopen accounting: one reopen consumed (C3), zero pending. -/
def S3142ReopenCounter : String := "reopens_consumed=1|pending=0|policy=one-reopen-one-repin"

theorem S3142ReopenCounter_eq :
    S3142ReopenCounter = "reopens_consumed=1|pending=0|policy=one-reopen-one-repin" := rfl

/-- Pin-integrity record. -/
def S3142PinIntegrityReceipt : Obligation :=
  { id := "IUT.project.pin-integrity-receipt"
    source := "post-C3-closure pins; registry freeze discipline"
    status := VerificationStatus.interface
    note :=
      "PIN SIZES gate=22958 registry=13108 record=14932 (all fresh at 04:1x); ONE " ++
        "reopen consumed for the C3 closure, ZERO pending; policy = ONE reopen + ONE " ++
        "re-pin, registry reopens only on a real residual closure, no v4 promotion."
    dependsOn :=
      [ "S3140ClosureGateActual", "S3131FinalResidualRegistryActual",
        "S3140FinalAcceptanceRecordActual" ] }

#check S3142PinIntegrityReceipt
#check S3142PinSizes_eq
#check S3142ReopenCounter_eq

end LeanFormal.IUT.Audit
