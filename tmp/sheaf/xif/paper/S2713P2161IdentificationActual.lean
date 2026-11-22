import tmp.sheaf.xif.paper.S2709IdealFactorizationActual
import tmp.sheaf.xif.paper.S2708AbsNorm2161Actual
import tmp.sheaf.xif.paper.S2698ResidueNorm2161Actual
import tmp.sheaf.xif.paper.S2701GaussianPrimeIdealsActual

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S2698ResidueNorm2161Actual
open LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2708AbsNorm2161Actual
open LeanFormal.IUT.XiFPaper.S2709IdealFactorizationActual

namespace LeanFormal.IUT.XiFPaper.S2713P2161IdentificationActual

local instance s2713GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2713Fact2161 : Fact (Nat.Prime 2161) := ⟨by decide⟩

theorem S2713_primeOver_dvd_2161 :
    S2696PrimeOver.ideal ∣ Ideal.span {(2161 : GaussianO)} := by
  haveI : S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}) :=
    S2698PrimeOver_liesOver_span
  haveI : (Ideal.span {(2161 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2161
  have hne : S2696PrimeOver.ideal ≠ ⊤ := S2696PrimeOver.isMaximal.ne_top
  have hdiv := (Ideal.liesOver_iff_dvd_map (P := S2696PrimeOver.ideal) hne).mp
    (inferInstance : S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}))
  rw [Ideal.map_span, Set.image_singleton] at hdiv
  simpa using hdiv

theorem S2713_primeOver_eq_plus_or_minus :
    S2696PrimeOver.ideal = gaussianField2161Plus ∨
      S2696PrimeOver.ideal = gaussianField2161Minus := by
  haveI : S2696PrimeOver.ideal.IsPrime := S2696PrimeOver.isMaximal.isPrime
  exact S2709_prime_dvd_2161 S2696PrimeOver.ideal S2713_primeOver_dvd_2161

theorem S2713_absNorm : Ideal.absNorm S2696PrimeOver.ideal = 2161 := by
  rcases S2713_primeOver_eq_plus_or_minus with h | h
  · rw [h]; exact gaussianField2161Plus_absNorm
  · rw [h]; exact gaussianField2161Minus_absNorm

theorem S2713_inertiaDeg_eq_one :
    (Ideal.span {(2161 : ℤ)}).inertiaDeg' S2696PrimeOver.ideal = 1 := by
  haveI : S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}) :=
    S2698PrimeOver_liesOver_span
  exact S2708_inertiaDeg_eq_one_of_absNorm S2696PrimeOver.ideal S2713_absNorm

theorem S2713_residueNormBase :
    residueNormBase S2696GaussianPlace = 2161 := by
  unfold residueNormBase
  rw [S2696GaussianPlace_maximalIdeal, S2713_absNorm]
  norm_num

#check S2713_primeOver_eq_plus_or_minus
#check S2713_absNorm
#check S2713_inertiaDeg_eq_one
#check S2713_residueNormBase
#print axioms S2713_primeOver_eq_plus_or_minus
#print axioms S2713_residueNormBase
end LeanFormal.IUT.XiFPaper.S2713P2161IdentificationActual
end
