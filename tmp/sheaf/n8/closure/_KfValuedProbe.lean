import tmp.sheaf.n8.closure.EtaNontriviallyNormedKfActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.NativeC3
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NormedField
variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
example : (Valued.v (R := LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual.Kf X)).IsNontrivial := inferInstance
example : Nonempty ((Valued.v (R := LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual.Kf X)).RankOne) := ⟨inferInstance⟩
end