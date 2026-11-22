import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace TestUnit
variable {K : Type} [Field K] [NumberField K] (v : NumberField.FinitePlace K)

noncomputable abbrev R := NumberField.RingOfIntegers K
noncomputable abbrev C (v : NumberField.FinitePlace K) := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v.maximalIdeal

example (hp : residueCharacteristic v ≠ 0) :
    CharP (IsLocalRing.ResidueField (C v)) (residueCharacteristic v) := by
  let e := adicCompletionResidueQuotientEquiv (K := K) v.maximalIdeal
  haveI hsrc : CharP (R ⧸ v.maximalIdeal.asIdeal) (residueCharacteristic v) := by
    unfold residueCharacteristic ResidueField
    infer_instance
  exact CharP.of_ringHom_of_ne_zero (e : (R ⧸ v.maximalIdeal.asIdeal) →+* (C v ⧸ IsLocalRing.maximalIdeal (C v)))
    (residueCharacteristic v) hp
end TestUnit
