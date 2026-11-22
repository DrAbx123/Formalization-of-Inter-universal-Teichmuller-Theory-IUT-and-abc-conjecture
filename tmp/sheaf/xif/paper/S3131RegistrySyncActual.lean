import tmp.sheaf.xif.paper.S3131FinalResidualRegistryActual
import tmp.sheaf.xif.paper.S3131RegistryLengthActual
import tmp.sheaf.xif.paper.S3131RegistryABCStrengthActual
import tmp.sheaf.xif.paper.S3131RegistryGateOwnersActual

/-! # S3131: registry export sync (gate identifier check)

Import hub for the closure gate: pulls every registry declaration and checks
the exact names the gate needs (length / ABC-strength / owner list).
-/

open LeanFormal.IUT.Audit

#check S3131FinalResidualRegistry
#check S3131FinalResidualRegistry_length
#check S3131ABCStrengthResiduals
#check S3131ABCStrengthResiduals_length
#check S3131RegistryGateOwners
#check S3131RegistryGateOwners_length

-- list API on the owner list (resolves gate references to .length/.map)
#check S3131RegistryGateOwners.length
#check S3131RegistryGateOwners.map
