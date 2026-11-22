import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace TestUnit
variable {K : Type} [Field K] [NumberField K] (v : NumberField.FinitePlace K)

abbrev R := NumberField.RingOfIntegers K
abbrev C := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v.maximalIdeal

example (hp : residueCharacteristic v ≠ 0) :
    CharP (IsLocalRing.ResidueField C) (residueCharacteristic v) := by
  let e := adicCompletionResidueQuotientEquiv (K := K) v.maximalIdeal
  haveI hsrc : CharP (R ⧸ v.maximalIdeal.asIdeal) (residueCharacteristic v) := by
    unfold residueCharacteristic ResidueField
    infer_instance
  exact CharP.of_ringHom_of_ne_zero (e : (R ⧸ v.maximalIdeal.asIdeal) →+* (C ⧸ IsLocalRing.maximalIdeal C))
    (residueCharacteristic v) hp
end TestUnit
