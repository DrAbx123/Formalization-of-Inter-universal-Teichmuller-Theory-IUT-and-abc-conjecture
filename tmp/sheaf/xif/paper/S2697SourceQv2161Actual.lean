import tmp.sheaf.xif.paper.S2687Split2161Actual
import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual
import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2697SourceQv2161Actual

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

abbrev O := NumberField.RingOfIntegers GaussianField
abbrev RO := NumberField.RingOfIntegers ℚ

/-- Algebra map compatibility between Z -> O and RO -> O via
`Rat.ringOfIntegersEquiv`. -/
theorem S2697_algebraMap_bridge (z : ℤ) :
    (algebraMap ℤ O z) =
      algebraMap RO O (Rat.ringOfIntegersEquiv.symm z) := by
  apply NumberField.RingOfIntegers.coe_injective
  simp

/-- Ideal-level bridge: comap along RO -> O equals comap along Z -> O
composed with `Rat.ringOfIntegersEquiv`. -/
theorem S2697_comap_bridge (I : Ideal O) :
    Ideal.comap (algebraMap RO O) I =
      Ideal.comap (Rat.ringOfIntegersEquiv : RO →+* ℤ)
        (Ideal.comap (algebraMap ℤ O) I) := by
  ext y
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
  rw [← S2697_algebraMap_bridge (Rat.ringOfIntegersEquiv y)]
  simp

/-- The rational place underlying S2696GaussianPlace is `concrete2161Place`. -/
theorem S2697_comap_place_eq :
    NumberFieldFinitePlace.comap (k := ℚ) S2696GaussianPlace =
      concrete2161Place := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  rw [S2697_comap_bridge]
  rw [show Ideal.comap (algebraMap ℤ O)
      S2696GaussianPlace.maximalIdeal.asIdeal =
      S2696IntegerPrimeIdeal from S2696GaussianPlace_liesOverInteger.symm]
  rw [S2696IntegerPrimeIdeal, concrete2161Place_maximalIdeal]
  rw [← Rat.HeightOneSpectrum.span_natGenerator]
  rw [concrete2161HeightOne_natGenerator]
  rfl

/-- Split multiplicative reduction at the Gaussian place above 2161. -/
theorem S2697_hasSplitMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      S2696GaussianPlace := by
  refine PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    concreteSplitPuncturedCurve S2696GaussianPlace ?_
  rw [S2697_comap_place_eq]
  exact concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_2161

/-- Actual source q_v at the Gaussian place above 2161. -/
noncomputable def S2697SourceQv2161 :
    SourceQvClosed.SourceQv
      (K := NormalizedCompletion S2696GaussianPlace)
      ((concreteSplitPuncturedCurve.baseChange GaussianField).baseChange
        (NormalizedCompletion S2696GaussianPlace)).curve
      ((concreteSplitPuncturedCurve.baseChange GaussianField).baseChange
        (NormalizedCompletion S2696GaussianPlace)).isElliptic :=
  Classical.choice (SourceQvClosed.exists_sourceQv_at_finitePlace_closed
    S2696GaussianPlace (concreteSplitPuncturedCurve.baseChange GaussianField)
    S2697_hasSplitMultiplicativeReductionAt)

#check S2697_algebraMap_bridge
#check S2697_comap_bridge
#check S2697_comap_place_eq
#check S2697_hasSplitMultiplicativeReductionAt
#check S2697SourceQv2161
#print axioms S2697_comap_place_eq
#print axioms S2697_hasSplitMultiplicativeReductionAt

end LeanFormal.IUT.XiFPaper.S2697SourceQv2161Actual
end