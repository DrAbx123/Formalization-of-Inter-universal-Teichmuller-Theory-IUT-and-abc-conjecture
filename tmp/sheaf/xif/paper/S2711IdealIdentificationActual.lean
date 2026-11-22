import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual
import tmp.sheaf.xif.paper.S2709IdealFactorizationActual
import tmp.sheaf.xif.paper.S2710LiesOverDvdActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
set_option maxRecDepth 100000
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2709IdealFactorizationActual
open LeanFormal.IUT.XiFPaper.S2710LiesOverDvdActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

namespace LeanFormal.IUT.XiFPaper.S2711IdealIdentificationActual

local instance s2711GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The arbitrary prime of the Gaussian integers over 2161 is one of the two
explicit factors of (2161). -/
theorem S2711_ideal_eq_plus_or_minus :
    S2696PrimeOver.ideal = gaussianField2161Plus ∨
      S2696PrimeOver.ideal = gaussianField2161Minus := by
  haveI : S2696PrimeOver.ideal.IsPrime := S2696PrimeOver.isMaximal.isPrime
  exact S2709_prime_dvd_2161 S2696PrimeOver.ideal S2710_primeOver_dvd_span2161

/-- The absolute norm of the arbitrary prime over 2161 is exactly 2161. -/
theorem S2711_absNorm :
    S2696PrimeOver.ideal.absNorm = 2161 := by
  rcases S2711_ideal_eq_plus_or_minus with h | h
  · rw [h]
    exact gaussianField2161Plus_absNorm
  · rw [h]
    exact gaussianField2161Minus_absNorm

/-- The residue norm base of the corresponding finite place is exactly 2161. -/
theorem S2711_residueNormBase :
    residueNormBase S2696GaussianPlace = (2161 : ℝ) := by
  unfold residueNormBase
  rw [S2696GaussianPlace_maximalIdeal]
  change (S2696PrimeOver.ideal.absNorm : ℝ) = (2161 : ℝ)
  rw [S2711_absNorm]
  norm_num

/-- The corresponding finite place is one of the two explicit S2701 places. -/
theorem S2711_place_eq_plus_or_minus :
    S2696GaussianPlace = gaussianField2161PlusPlace ∨
      S2696GaussianPlace = gaussianField2161MinusPlace := by
  rcases S2711_ideal_eq_plus_or_minus with h | h
  · left
    apply NumberField.FinitePlace.maximalIdeal_injective
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [S2696GaussianPlace_maximalIdeal, gaussianField2161PlusPlace_maximalIdeal]
    exact h
  · right
    apply NumberField.FinitePlace.maximalIdeal_injective
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [S2696GaussianPlace_maximalIdeal, gaussianField2161MinusPlace_maximalIdeal]
    exact h

/-- The residue characteristic of the corresponding finite place is 2161. -/
theorem S2711_residueCharacteristic :
    residueCharacteristic S2696GaussianPlace = 2161 := by
  rcases S2711_place_eq_plus_or_minus with h | h
  · rw [h]
    exact gaussianField2161PlusPlace_residueCharacteristic
  · rw [h]
    exact gaussianField2161MinusPlace_residueCharacteristic

/-- Degree-one form: residue norm base equals residue characteristic. -/
theorem S2711_residueNormBase_eq_residueCharacteristic :
    residueNormBase S2696GaussianPlace =
      (residueCharacteristic S2696GaussianPlace : ℝ) := by
  rw [S2711_residueNormBase, S2711_residueCharacteristic]
  norm_num

#check S2711_ideal_eq_plus_or_minus
#check S2711_absNorm
#check S2711_residueNormBase
#check S2711_place_eq_plus_or_minus
#check S2711_residueCharacteristic
#check S2711_residueNormBase_eq_residueCharacteristic
#print axioms S2711_ideal_eq_plus_or_minus
#print axioms S2711_absNorm
#print axioms S2711_residueNormBase
#print axioms S2711_residueNormBase_eq_residueCharacteristic

end LeanFormal.IUT.XiFPaper.S2711IdealIdentificationActual
end
