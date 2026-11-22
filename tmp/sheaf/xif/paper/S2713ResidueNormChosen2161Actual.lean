import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual
import tmp.sheaf.xif.paper.S2698ResidueNorm2161Actual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
set_option maxRecDepth 100000
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S2698ResidueNorm2161Actual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2713ResidueNormChosen2161Actual

local instance s2713GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2713_primeOver_dvd_span2161 :
    S2696PrimeOver.ideal ∣
      Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)} := by
  haveI hlies : S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}) := by
    simpa [S2696IntegerPrimeIdeal] using S2696PrimeOver.liesOver
  have hmemInt : algebraMap ℤ (NumberField.RingOfIntegers GaussianField) (2161 : ℤ) ∈
      S2696PrimeOver.ideal := by
    have h : (2161 : ℤ) ∈ Ideal.span {(2161 : ℤ)} := Ideal.mem_span_singleton_self 2161
    rw [S2696GaussianPlace_liesOverInteger] at h
    simpa only [Ideal.mem_comap] using h
  have hmem : (2161 : NumberField.RingOfIntegers GaussianField) ∈
      S2696PrimeOver.ideal := by
    simpa using hmemInt
  have hle : Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)} ≤
      S2696PrimeOver.ideal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  exact (Ideal.dvd_iff_le).mpr hle

theorem S2713_absNorm_primeOver_eq_2161 :
    Ideal.absNorm S2696PrimeOver.ideal = 2161 := by
  have hle : Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)} ≤
      S2696PrimeOver.ideal :=
    Ideal.dvd_iff_le.mp S2713_primeOver_dvd_span2161
  have hdvd : Ideal.absNorm S2696PrimeOver.ideal ∣
      Ideal.absNorm (Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)}) :=
    Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hge : 2161 ≤ Ideal.absNorm S2696PrimeOver.ideal :=
    S2698_residueNormBase_ge
  have hle2161 : Ideal.absNorm S2696PrimeOver.ideal ≤ 2161 :=
    Nat.le_of_dvd (by norm_num) (by simpa using hdvd)
  omega

theorem S2713_residueNormBase_eq_2161 :
    residueNormBase S2696GaussianPlace = 2161 := by
  unfold residueNormBase
  rw [S2696GaussianPlace_maximalIdeal]
  exact_mod_cast S2713_absNorm_primeOver_eq_2161

#check S2713_absNorm_primeOver_eq_2161
#check S2713_residueNormBase_eq_2161
#print axioms S2713_residueNormBase_eq_2161

end LeanFormal.IUT.XiFPaper.S2713ResidueNormChosen2161Actual
end
