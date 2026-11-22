import tmp.sheaf.xif.paper.S1695ResidueFiniteActual
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace LeanFormal.IUT.XiFPaper.S1696ResidueExponentActual
local instance s1696GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
theorem s1696GaussianResidueCard :
    Nat.card (NumberFieldFinitePlace.ResidueField
      concreteGaussianFivePlace) = 5 :=
  concreteGaussianFivePlaceResidueField_card
theorem s1696GaussianUnitsCard :
    Nat.card (NumberFieldFinitePlace.ResidueField
      concreteGaussianFivePlace)ˣ = 4 := by
  have hZ : Nat.card (ZMod 5)ˣ = 4 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  rw [← hZ]
  exact Nat.card_congr
    (Units.mapEquiv concreteGaussianFivePlaceResidueEquiv.toMulEquiv).toEquiv

theorem s1696GaussianGcd {l : PrimeGeFive} :
    Nat.gcd 4 (2 * l.value) = 2 := by
  have hodd : Odd l.value := l.prime.odd_of_ne_two (by
    have h5 := l.ge_five
    omega)
  have hcop : Nat.Coprime 2 l.value := Nat.coprime_two_left.mpr hodd
  have hgcd : Nat.gcd 2 l.value = 1 := hcop
  calc Nat.gcd 4 (2 * l.value) = Nat.gcd (2 * 2) (2 * l.value) := by norm_num
    _ = 2 * Nat.gcd 2 l.value := Nat.gcd_mul_left 2 2 l.value
    _ = 2 := by rw [hgcd, Nat.mul_one]
theorem s1696GaussianExponent {l : PrimeGeFive} :
    4 / Nat.gcd 4 (2 * l.value) = 2 := by
  rw [s1696GaussianGcd]
end LeanFormal.IUT.XiFPaper.S1696ResidueExponentActual
end
