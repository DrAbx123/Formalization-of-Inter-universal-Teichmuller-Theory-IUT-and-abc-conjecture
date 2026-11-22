import tmp.sheaf.n8.closure.EtaNNHullVolumeEqualityActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeEqualityActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
local instance : Module (ℤ_[nativePrime X]) (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  Module.compHom (CommonPrimeCompletion (nativeFPlaceAtPrime X)) (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]))
example : Submodule (ℤ_[nativePrime X]) (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  (1 : Submodule (Integers (CommonPrimeCompletion (nativeFPlaceAtPrime X))) (CommonPrimeCompletion (nativeFPlaceAtPrime X))).restrictScalars (ℤ_[nativePrime X])
