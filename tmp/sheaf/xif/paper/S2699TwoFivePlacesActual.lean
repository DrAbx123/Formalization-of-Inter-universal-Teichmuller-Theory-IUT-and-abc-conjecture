import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2699TwoFivePlacesActual

local instance s2699FiveFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance s2699GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

noncomputable def S2699GaussianPlaceFivePlus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianFieldFivePrimePlus
      isPrime := gaussianFieldFivePrimePlus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianFieldFivePrimePlus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

noncomputable def S2699GaussianPlaceFiveMinus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianFieldFivePrimeMinus
      isPrime := gaussianFieldFivePrimeMinus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianFieldFivePrimeMinus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

theorem S2699PlaceFivePlus_maximalIdeal :
    S2699GaussianPlaceFivePlus.maximalIdeal.asIdeal = gaussianFieldFivePrimePlus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

theorem S2699PlaceFiveMinus_maximalIdeal :
    S2699GaussianPlaceFiveMinus.maximalIdeal.asIdeal = gaussianFieldFivePrimeMinus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

theorem S2699ResidueCharacteristicPlus :
    NumberFieldFinitePlace.residueCharacteristic S2699GaussianPlaceFivePlus = 5 := by
  unfold NumberFieldFinitePlace.residueCharacteristic NumberFieldFinitePlace.ResidueField
  rw [S2699PlaceFivePlus_maximalIdeal]
  let e := gaussianFieldFivePrimePlusResidueEquiv
  have hzero : (5 : gaussianRingOfIntegers ⧸ gaussianFieldFivePrimePlus) = 0 := by
    apply e.injective
    rw [map_zero]
    change e ((5 : ℕ) : gaussianRingOfIntegers ⧸ gaussianFieldFivePrimePlus) = 0
    rw [map_natCast, ZMod.natCast_self]
  exact CharP.ringChar_of_prime_eq_zero Nat.prime_five hzero

theorem S2699ResidueCharacteristicMinus :
    NumberFieldFinitePlace.residueCharacteristic S2699GaussianPlaceFiveMinus = 5 := by
  unfold NumberFieldFinitePlace.residueCharacteristic NumberFieldFinitePlace.ResidueField
  rw [S2699PlaceFiveMinus_maximalIdeal]
  let e := gaussianFieldFivePrimeMinusResidueEquiv
  have hzero : (5 : gaussianRingOfIntegers ⧸ gaussianFieldFivePrimeMinus) = 0 := by
    apply e.injective
    rw [map_zero]
    change e ((5 : ℕ) : gaussianRingOfIntegers ⧸ gaussianFieldFivePrimeMinus) = 0
    rw [map_natCast, ZMod.natCast_self]
  exact CharP.ringChar_of_prime_eq_zero Nat.prime_five hzero

theorem S2699OddPlus :
    Odd (NumberFieldFinitePlace.residueCharacteristic S2699GaussianPlaceFivePlus) := by
  rw [S2699ResidueCharacteristicPlus]
  norm_num

theorem S2699OddMinus :
    Odd (NumberFieldFinitePlace.residueCharacteristic S2699GaussianPlaceFiveMinus) := by
  rw [S2699ResidueCharacteristicMinus]
  norm_num

#print axioms S2699ResidueCharacteristicPlus
#print axioms S2699OddPlus

end LeanFormal.IUT.XiFPaper.S2699TwoFivePlacesActual
end
