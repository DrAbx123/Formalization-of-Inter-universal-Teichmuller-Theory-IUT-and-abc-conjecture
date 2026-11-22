import tmp.sheaf.xif.paper.S2699TwoFivePlacesActual
import tmp.sheaf.xif.paper.S2704GaussianPrimeActual
import tmp.sheaf.xif.paper.S1712OddResidueActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2699TwoFivePlacesActual
open LeanFormal.IUT.XiFPaper.S2704GaussianPrimeActual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2700FivePlaceComapBridgeActual

local instance s2700FiveFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance s2700GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2700ComapPlus :
    NumberFieldFinitePlace.comap (k := ℚ) S2699GaussianPlaceFivePlus =
      concreteFivePlace := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  change (S2699GaussianPlaceFivePlus.maximalIdeal.asIdeal).under
      (NumberField.RingOfIntegers ℚ) =
    (concreteFivePlace.maximalIdeal).asIdeal
  rw [S2699PlaceFivePlus_maximalIdeal,
    gaussianFieldFivePrimePlus_under_rational,
    concreteFivePlace_maximalIdeal,
    concreteFiveHeightOne_asIdeal_eq_span]

theorem S2700ComapMinus :
    NumberFieldFinitePlace.comap (k := ℚ) S2699GaussianPlaceFiveMinus =
      concreteFivePlace := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  change (S2699GaussianPlaceFiveMinus.maximalIdeal.asIdeal).under
      (NumberField.RingOfIntegers ℚ) =
    (concreteFivePlace.maximalIdeal).asIdeal
  rw [S2699PlaceFiveMinus_maximalIdeal,
    gaussianFieldFivePrimeMinus_under_rational,
    concreteFivePlace_maximalIdeal,
    concreteFiveHeightOne_asIdeal_eq_span]

theorem S2700ResidueCharacteristicPlus_via_comap :
    NumberFieldFinitePlace.residueCharacteristic S2699GaussianPlaceFivePlus = 5 := by
  rw [S2704_residueCharacteristic_of_comap S2699GaussianPlaceFivePlus
    concreteFivePlace S2700ComapPlus,
    S1712ConcreteFivePlace_residueCharacteristic]

theorem S2700ResidueCharacteristicMinus_via_comap :
    NumberFieldFinitePlace.residueCharacteristic S2699GaussianPlaceFiveMinus = 5 := by
  rw [S2704_residueCharacteristic_of_comap S2699GaussianPlaceFiveMinus
    concreteFivePlace S2700ComapMinus,
    S1712ConcreteFivePlace_residueCharacteristic]

#print axioms S2700ComapPlus
#print axioms S2700ResidueCharacteristicPlus_via_comap

end LeanFormal.IUT.XiFPaper.S2700FivePlaceComapBridgeActual
end
