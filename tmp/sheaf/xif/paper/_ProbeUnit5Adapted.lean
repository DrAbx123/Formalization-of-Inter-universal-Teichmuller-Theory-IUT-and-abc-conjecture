import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace TestUnit
variable {K : Type} [Field K] [NumberField K] (v : NumberField.FinitePlace K)

noncomputable abbrev R := NumberField.RingOfIntegers K
noncomputable abbrev C (v : NumberField.FinitePlace K) := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v.maximalIdeal

theorem test_charP :
    CharP (IsLocalRing.ResidueField (C v)) (residueCharacteristic v) := by
  let e := adicCompletionResidueQuotientEquiv (K := K) v.maximalIdeal
  haveI hsrc : CharP (R ⧸ v.maximalIdeal.asIdeal) (residueCharacteristic v) := by
    unfold residueCharacteristic ResidueField
    infer_instance
  exact CharP.of_ringHom_of_ne_zero (e : (R ⧸ v.maximalIdeal.asIdeal) →+* (C v ⧸ IsLocalRing.maximalIdeal (C v)))
    (residueCharacteristic v) (residueCharacteristic_prime v).ne_zero

example (n : Nat) : IsUnit ((n : C v)) ↔ ¬ residueCharacteristic v ∣ n := by
  haveI := test_charP (K := K) v
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  rw [show IsLocalRing.residue (C v) (n : C v) = (n : IsLocalRing.ResidueField (C v)) by simp]
  exact not_congr (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField (C v)) (residueCharacteristic v) n)
end TestUnit
