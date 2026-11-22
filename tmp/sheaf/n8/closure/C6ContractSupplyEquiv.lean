import tmp.sheaf.n8.closure.C6ConstructedBridge
import tmp.sheaf.n8.closure.C10DonorSearch

/-! # The two native contract-supply notions agree

`C6ConstructedBridge.C6ContractSupply X` and
`C10DonorSearch.NativeContractSupply X` both say: there exists a
`SourceDefinition31Data` over `X.S.arithmetic`. This file records the
definitional equivalence, so the C10 native contract supply is exactly the C6
input donor.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C6ConstructedBridge
open LeanFormal.IUT.N8Closure.C10DonorSearch

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The C6 contract supply is exactly the C10 native contract supply. -/
theorem c6ContractSupply_iff_nativeContractSupply :
    C6ContractSupply X ↔ NativeContractSupply X :=
  Iff.rfl

end LeanFormal.IUT.N8Closure.C1Actual
end