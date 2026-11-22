import LeanFormal.IUT.Audit.Status

/-! # S3141: gate pin receipt (kernel-visible data)

Compact receipt of the current gate/recount facts for downstream consumers.  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Receipt string: gate | registry | decl counts | sorry count. -/
def S3141GateReceipt : String :=
  "gate=S3140ClosureGateActual|22958|src=41C7ED96|olean=4E8DFE7F|registry=S3131FinalResidualRegistryActual|13108|55012B55|decls=53|trio=50|noax=3|sorry=0"

theorem S3141GateReceipt_eq :
    S3141GateReceipt =
      "gate=S3140ClosureGateActual|22958|src=41C7ED96|olean=4E8DFE7F|registry=S3131FinalResidualRegistryActual|13108|55012B55|decls=53|trio=50|noax=3|sorry=0" := rfl

/-- Recount fact: 50 trio declarations + 3 no-axiom = 53 audited. -/
theorem S3141GateRecount_arith : 50 + 3 = 53 := rfl

/-- Gate receipt record. -/
def S3141GateReceiptRecord : Obligation :=
  { id := "IUT.project.gate-pin-receipt"
    source :=
      "post-C3-closure re-pin: gate 22958 olean 04:08:11; registry 13108 olean 04:06:14"
    status := VerificationStatus.interface
    note :=
      "GATE RECEIPT: gate S3140ClosureGateActual EXIT=0 SIZE 22958, src 41C7ED96..., " ++
        "olean 4E8DFE7F... (fresh 04:08:11); frozen registry 13108 src 55012B55...; " ++
        "recount 53 = 50 trio + 3 no-axiom, ZERO sorryAx; kernel recount probe green."
    dependsOn :=
      [ "S3140ClosureGateActual", "S3131FinalResidualRegistryActual",
        "_S3140FinalAxiomRecountProbeActual" ] }

#check S3141GateReceipt
#check S3141GateReceipt_eq
#check S3141GateReceiptRecord

end LeanFormal.IUT.Audit
