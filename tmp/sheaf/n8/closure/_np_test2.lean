import tmp.sheaf.n8.closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
example {l : PrimeGeFive} (X : N8NativeInput l) (v : NativeSelectedPlaces X) : Nat :=
  match v.1 with
  | NumberFieldPlace.finite p => 1
  | NumberFieldPlace.infinite w => 0
