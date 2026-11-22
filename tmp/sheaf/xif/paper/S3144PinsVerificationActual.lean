import LeanFormal.IUT.Audit.Status

/-! # S3144: pins verification (after M2a second closure)

Kernel-visible pin strings for the current acceptance pair.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Gate pin string (post-M2a re-pin). -/
def S3144GatePin : String :=
  "S3140ClosureGateActual|23066|7A90365426ACB93DFC7AC429414823F76A27AFEDC03A44A3729574591F9F2191|4E8DFE7F1522AEE45775CF383123D1169E2F2AB0DA8C9AB6753F872EE76F34EE"

theorem S3144GatePin_eq :
    S3144GatePin =
      "S3140ClosureGateActual|23066|7A90365426ACB93DFC7AC429414823F76A27AFEDC03A44A3729574591F9F2191|4E8DFE7F1522AEE45775CF383123D1169E2F2AB0DA8C9AB6753F872EE76F34EE" := rfl

/-- Registry pin string (frozen 13129). -/
def S3144RegistryPin : String :=
  "S3131FinalResidualRegistryActual|13129|0518E5322D2BCC7D22DA692894B5D844EAA81D5741AB094CA51421A85E567CD3|04:19:43"

theorem S3144RegistryPin_eq :
    S3144RegistryPin =
      "S3131FinalResidualRegistryActual|13129|0518E5322D2BCC7D22DA692894B5D844EAA81D5741AB094CA51421A85E567CD3|04:19:43" := rfl

/-- Record pin string (post-M2a). -/
def S3144RecordPin : String :=
  "S3140FinalAcceptanceRecordActual|15501|23525F60735E2B8F0FC7A3373DA0A1F113905D7F92847A73271E59B6F044EF7C|359EA7974BC4A0C216B583D420FF8784C91A086DB703C1155C2CA0180592A7C0"

theorem S3144RecordPin_eq :
    S3144RecordPin =
      "S3140FinalAcceptanceRecordActual|15501|23525F60735E2B8F0FC7A3373DA0A1F113905D7F92847A73271E59B6F044EF7C|359EA7974BC4A0C216B583D420FF8784C91A086DB703C1155C2CA0180592A7C0" := rfl

/-- Pins verification record (post-M2a closure). -/
def S3144PinsVerification : Obligation :=
  { id := "IUT.project.pins-verification-m2a"
    source := "post-M2a single re-pin 2026-11-10 04:25"
    status := VerificationStatus.interface
    note :=
      "PINS (post M2a closure): gate 23066 (7A903654..., olean 4E8DFE7F..., olean 04:22:12 " ++
        "> registry 04:19:43); registry 13129 (0518E532..., 15 ids/order/ABC unchanged); " ++
        "record 15501 (23525F60..., olean 359EA797...; M2a+C3 CLOSED folded; R1.M1 OPEN; " ++
        "A12/A13 unchanged; no v4). Kernel recount 53=50 trio+3 no-ax, zero sorryAx."
    dependsOn :=
      [ "S3140ClosureGateActual", "S3131FinalResidualRegistryActual",
        "S3140FinalAcceptanceRecordActual" ] }

#check S3144PinsVerification
#check S3144GatePin_eq
#check S3144RegistryPin_eq
#check S3144RecordPin_eq

end LeanFormal.IUT.Audit
