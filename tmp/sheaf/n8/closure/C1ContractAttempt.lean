import tmp.sheaf.n8.closure.P6BridgeActual
import tmp.sheaf.n8.closure.C1BridgeProof

/-!
# C1 contract attempt: P6BridgeDonors / native contract datum

Reuses `P6BridgeActual` and `C1BridgeProof`.  Actual native partial data
(place/selected) is constructed; the contract datum and old R/fiber binding
are not.  Conditional exact no-go and the full donor named obligation are
recorded.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1ContractAttempt

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C1BridgeProof
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.P6BridgeActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- Actual native place/selected data (zero sorry). -/
noncomputable def c1ContractActualPartial (X : N8NativeInput l) :
    P6ActualPartial X :=
  p6ActualPartial X

/-- Exact conditional no-go: an empty contract type rules out P6BridgeDonors. -/
theorem no_p6BridgeDonors_of_empty_contract (X : N8NativeInput l)
    (h : IsEmpty (SourceDefinition31Data.{0} l)) :
    IsEmpty (P6BridgeDonors X) :=
  P6BridgeActual.no_p6BridgeDonors_of_empty_contract X h

end LeanFormal.IUT.N8Closure.C1ContractAttempt