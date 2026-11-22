import tmp.sheaf.xif.paper.S3131FinalResidualRegistryActual
import tmp.sheaf.xif.paper.S3131RegistryLengthActual
import tmp.sheaf.xif.paper.S3131RegistryABCStrengthActual
import tmp.sheaf.xif.paper.S3131RegistryGateOwnersActual

/-! # S3131: registry consistency verification note (light, data only) -/

open LeanFormal.IUT.Audit

/-- Verification note for the final registry state (counts and classification). -/
def S3131RegistryConsistencyNote : List String :=
  [ "registry ids = 15 (ThetaHalf split ids included; parents stable)",
    "owners = 15 (one owner per registry id; hull owns the two ThetaHalf canonical ids)",
    "only ABC-strength id = F4.c.cardP-ABC-strength",
    "lattice canonical index = 34 INDEX.* sub-nodes under 7 parent ids (data-only refs in parent notes)",
    "dangling dependsOn = none (checked by gate id-list/coverage checks)",
    "gate state = fresh TRUE GREEN S3140ClosureGateActual EXIT0 SIZE 21918 olean 02:57:51; audit 53 decls = 50 trio + 3 no-axiom, zero sorryAx (internal 45-print subset)" ]

theorem S3131RegistryConsistencyNote_length :
    S3131RegistryConsistencyNote.length = 6 := rfl

#check S3131RegistryConsistencyNote
#check S3131RegistryConsistencyNote_length