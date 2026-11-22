import tmp.sheaf.n8.closure.EtaPStepNormLink
import tmp.sheaf.n8.closure.C3TensorTargetCorrection

noncomputable section

namespace LeanFormal.IUT.N8Closure.PStepSpecializeProbe

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

example : NormedAlgebra ℚ_[nativePrime X] (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  inferInstance

example : FiniteDimensional ℚ_[nativePrime X] (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  inferInstance

example : LocallyCompactSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  inferInstance

example : IsUltrametricDist (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  inferInstance

example : MeasurableSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  borel _

example : BorelSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X)) := ⟨rfl⟩

example : NontriviallyNormedField (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  inferInstance

example : (Valued.v : Valuation (CommonPrimeCompletion (nativeFPlaceAtPrime X)) ℤᵐ⁰).IsNontrivial :=
  inferInstance

end LeanFormal.IUT.N8Closure.PStepSpecializeProbe