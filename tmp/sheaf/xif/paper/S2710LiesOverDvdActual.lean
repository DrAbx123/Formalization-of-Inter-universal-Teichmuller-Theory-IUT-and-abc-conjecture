import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual

noncomputable section
set_option maxRecDepth 100000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual

namespace LeanFormal.IUT.XiFPaper.S2710LiesOverDvdActual

local instance s2710GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2710_primeOver_dvd_span2161 :
    S2696PrimeOver.ideal ∣
      Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)} := by
  haveI hlies : S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}) := by
    simpa [S2696IntegerPrimeIdeal] using S2696PrimeOver.liesOver
  have hmemInt : algebraMap ℤ (NumberField.RingOfIntegers GaussianField) (2161 : ℤ) ∈
      S2696PrimeOver.ideal :=
    (Ideal.mem_of_liesOver S2696PrimeOver.ideal (Ideal.span {(2161 : ℤ)}) (2161 : ℤ)).mp
      (Ideal.mem_span_singleton_self 2161)
  have hmem : (2161 : NumberField.RingOfIntegers GaussianField) ∈
      S2696PrimeOver.ideal := by
    simpa using hmemInt
  have hle : Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)} ≤
      S2696PrimeOver.ideal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  exact (Ideal.dvd_iff_le).mpr hle

theorem S2710_dvd_span_of_mem
    (P : Ideal (NumberField.RingOfIntegers GaussianField))
    (hmem : (2161 : NumberField.RingOfIntegers GaussianField) ∈ P) :
    P ∣ Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)} :=
  (Ideal.dvd_iff_le).mpr (by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem)

#check S2710_primeOver_dvd_span2161
#check S2710_dvd_span_of_mem
#print axioms S2710_primeOver_dvd_span2161
#print axioms S2710_dvd_span_of_mem

end LeanFormal.IUT.XiFPaper.S2710LiesOverDvdActual
end
