import tmp.sheaf.n8.closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal NormedField
variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
#check (Valued.v (R := LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual.Kf X))
#check (inferInstance : Valued (LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual.Kf X) ℝ≥0)
#check (inferInstance : Valuation.RankLeOne (NormedField.valuation (K := LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual.Kf X)))
#check (inferInstance : Valuation.RankLeOne (Valued.v (R := LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual.Kf X)))
end