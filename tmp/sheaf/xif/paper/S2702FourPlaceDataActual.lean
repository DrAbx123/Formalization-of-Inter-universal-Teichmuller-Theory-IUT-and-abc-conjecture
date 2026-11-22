import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2702FourPlaceDataActual

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

abbrev O := NumberField.RingOfIntegers GaussianField

/-- The second Gaussian place above 5, from the explicit ideal (2-i). -/
noncomputable def S2702Place5b : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianFieldFivePrimeMinus
      isPrime := gaussianFieldFivePrimeMinus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianFieldFivePrimeMinus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

theorem S2702Place5b_under :
    S2702Place5b.maximalIdeal.asIdeal.under ℤ = Ideal.span {(5 : ℤ)} := by
  rw [S2702Place5b, NumberField.FinitePlace.maximalIdeal_mk]
  exact gaussianFieldFivePrimeMinus_under

theorem S2702Place2161b_under :
    S2696GaussianPlace.maximalIdeal.asIdeal.under ℤ = Ideal.span {(2161 : ℤ)} := by
  rw [Ideal.under_def]
  exact S2696GaussianPlace_liesOverInteger.symm

/-- A rational prime p extracted from the ideal under a place. -/
theorem S2702_residueCharacteristic_eq_of_under
    (place : NumberField.FinitePlace GaussianField) (p : ℕ)
    (hunder : place.maximalIdeal.asIdeal.under ℤ = Ideal.span {(p : ℤ)}) :
    NumberFieldFinitePlace.residueCharacteristic place = p := by
  have hres := NumberFieldFinitePlace.under_eq_span_residueCharacteristic place
  have hEq : Ideal.span {(NumberFieldFinitePlace.residueCharacteristic place : ℤ)} =
      Ideal.span {(p : ℤ)} := by
    rw [← hres, hunder]
  have hdvd1 : (NumberFieldFinitePlace.residueCharacteristic place : ℤ) ∣ (p : ℤ) := by
    apply Ideal.mem_span_singleton.mp
    rw [hEq]
    exact Ideal.mem_span_singleton_self (p : ℤ)
  have hdvd2 : (p : ℤ) ∣ (NumberFieldFinitePlace.residueCharacteristic place : ℤ) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hEq]
    exact Ideal.mem_span_singleton_self _
  have hnat : NumberFieldFinitePlace.residueCharacteristic place ∣ p := by
    exact_mod_cast hdvd1
  have hnat2 : p ∣ NumberFieldFinitePlace.residueCharacteristic place := by
    exact_mod_cast hdvd2
  exact Nat.dvd_antisymm hnat hnat2

theorem S2702Place5b_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S2702Place5b = 5 :=
  S2702_residueCharacteristic_eq_of_under S2702Place5b 5 S2702Place5b_under

theorem S2702Place2161b_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S2696GaussianPlace = 2161 :=
  S2702_residueCharacteristic_eq_of_under S2696GaussianPlace 2161 S2702Place2161b_under

theorem S2702Place5a_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic concreteGaussianFivePlace = 5 :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic

noncomputable def S2702FourPlaceData : S2696FourPlaceData where
  p5a := concreteGaussianFivePlace
  p5b := S2702Place5b
  p2161a := S2696GaussianPlace2161
  p2161b := S2696GaussianPlace
  odd5a := by rw [S2702Place5a_residueCharacteristic]; norm_num
  odd5b := by rw [S2702Place5b_residueCharacteristic]; norm_num
  odd2161a := by rw [S2696GaussianPlace2161_residueCharacteristic]; norm_num
  odd2161b := by rw [S2702Place2161b_residueCharacteristic]; norm_num

#check S2702FourPlaceData
#print axioms S2702FourPlaceData

end LeanFormal.IUT.XiFPaper.S2702FourPlaceDataActual
end