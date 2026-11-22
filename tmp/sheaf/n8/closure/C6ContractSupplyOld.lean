import tmp.sheaf.n8.closure.C6ContractSupplyEquiv
import tmp.sheaf.n8.closure.C1BridgeProof

/-! # Old contract datum vs C6 contract supply

NativeContractDatumExists and C6ContractSupply are the same existential contract condition. The former also supplies NativeOriginalInputDonors once an index equivalence is chosen.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C6ConstructedBridge
open LeanFormal.IUT.N8Closure.C1BridgeProof
open LeanFormal.IUT.N8Closure.C10BridgeProof

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem nativeContractDatumExists_iff_c6ContractSupply :
    NativeContractDatumExists X ↔ C6ContractSupply X := Iff.rfl

noncomputable def nativeOriginalInputDonors_of_contract
    (h : NativeContractDatumExists X)
    (e : X.family.index ≃ SourceTheorem311Index) :
    NativeOriginalInputDonors X where
  initial := Classical.choose h
  initial_arithmetic := Classical.choose_spec h
  index_equiv := e

theorem nativeOriginalInputDonors_of_contract_initial
    (h : NativeContractDatumExists X)
    (e : X.family.index ≃ SourceTheorem311Index) :
    (nativeOriginalInputDonors_of_contract X h e).initial = Classical.choose h := rfl

end LeanFormal.IUT.N8Closure.C1Actual
end