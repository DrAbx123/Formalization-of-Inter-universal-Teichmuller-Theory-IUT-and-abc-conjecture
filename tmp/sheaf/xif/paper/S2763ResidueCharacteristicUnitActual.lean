import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2763ResidueCharacteristicUnitActual

variable {K : Type} [Field K] [NumberField K] (v : NumberField.FinitePlace K)

noncomputable abbrev LocalIntegers : Type :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v.maximalIdeal

theorem localResidueCharP :
    CharP (IsLocalRing.ResidueField (LocalIntegers (K := K) v))
      (residueCharacteristic v) := by
  let e := adicCompletionResidueQuotientEquiv (K := K) v.maximalIdeal
  haveI hsrc : CharP (NumberField.RingOfIntegers K ⧸ v.maximalIdeal.asIdeal)
      (residueCharacteristic v) := by
    unfold residueCharacteristic ResidueField
    infer_instance
  exact CharP.of_ringHom_of_ne_zero
    (e : (NumberField.RingOfIntegers K ⧸ v.maximalIdeal.asIdeal) →+*
      (LocalIntegers (K := K) v ⧸
        IsLocalRing.maximalIdeal (LocalIntegers (K := K) v)))
    (residueCharacteristic v) (residueCharacteristic_prime v).ne_zero

theorem isUnit_natCast_adicCompletionIntegers_iff_not_dvd (n : Nat) :
    IsUnit ((n : LocalIntegers (K := K) v)) ↔
      ¬ residueCharacteristic v ∣ n := by
  haveI := localResidueCharP (K := K) v
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  rw [show IsLocalRing.residue (LocalIntegers (K := K) v)
      (n : LocalIntegers (K := K) v) =
        (n : IsLocalRing.ResidueField (LocalIntegers (K := K) v)) by simp]
  exact not_congr
    (CharP.cast_eq_zero_iff
      (IsLocalRing.ResidueField (LocalIntegers (K := K) v))
      (residueCharacteristic v) n)

theorem isUnit_sixtyFour_of_residueCharacteristic_ne_two
    (h2 : residueCharacteristic v ≠ 2) :
    IsUnit ((64 : Nat) : LocalIntegers (K := K) v) := by
  rw [isUnit_natCast_adicCompletionIntegers_iff_not_dvd]
  intro hdvd
  have h64 : residueCharacteristic v ∣ (64 : Nat) := hdvd
  have hpow : residueCharacteristic v ∣ (2 : Nat) ^ 6 := by
    simpa using h64
  have hprime : Nat.Prime (residueCharacteristic v) :=
    residueCharacteristic_prime v
  have h2dvd : residueCharacteristic v ∣ 2 :=
    (Nat.Prime.dvd_of_dvd_pow hprime hpow)
  have hp2 : (2 : Nat) = residueCharacteristic v :=
    (Nat.prime_two.dvd_iff_eq hprime.ne_one).mp h2dvd
  exact h2 hp2.symm

#check isUnit_natCast_adicCompletionIntegers_iff_not_dvd
#check isUnit_sixtyFour_of_residueCharacteristic_ne_two
#print axioms isUnit_sixtyFour_of_residueCharacteristic_ne_two

end LeanFormal.IUT.XiFPaper.S2763ResidueCharacteristicUnitActual
end
