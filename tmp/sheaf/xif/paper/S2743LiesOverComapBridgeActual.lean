import tmp.sheaf.xif.paper.S2739FinsetSupportActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2743LiesOverComapBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K] [Algebra ℚ K]

/-- The actual `LiesOver` bridge for the chosen support place: the maximal ideal
of the chosen K-place lies over the maximal ideal of the rational place. -/
theorem S2743_supportPlace_liesOver (x : ℚ) (i : SupportIndex x) :
    Ideal.LiesOver (supportPlace (K := K) x i).maximalIdeal.asIdeal
      (letI : Fact (Nat.Prime i.1) :=
        ⟨prime_of_mem_arithmeticPrimeSupport i.2⟩
       (rationalFinitePlace i.1).maximalIdeal.asIdeal) := by
  letI : Fact (Nat.Prime i.1) :=
    ⟨prime_of_mem_arithmeticPrimeSupport i.2⟩
  rw [Ideal.liesOver_iff, Ideal.under_def]
  rw [← NumberFieldFinitePlace.comap_maximalIdeal
    (k := ℚ) (K := K) (place := supportPlace (K := K) x i)]
  rw [supportPlace_comap]
  simp [supportRationalPlace]

/-- Comap form: the underlying prime of the chosen place is the rational-prime
ideal. -/
theorem S2743_supportPlace_under (x : ℚ) (i : SupportIndex x) :
    Ideal.under (NumberField.RingOfIntegers ℚ)
        (supportPlace (K := K) x i).maximalIdeal.asIdeal =
      (letI : Fact (Nat.Prime i.1) :=
        ⟨prime_of_mem_arithmeticPrimeSupport i.2⟩
       (rationalFinitePlace i.1).maximalIdeal.asIdeal) := by
  letI : Fact (Nat.Prime i.1) :=
    ⟨prime_of_mem_arithmeticPrimeSupport i.2⟩
  rw [Ideal.under_def (NumberField.RingOfIntegers ℚ)]
  rw [← NumberFieldFinitePlace.comap_maximalIdeal
    (k := ℚ) (K := K) (place := supportPlace (K := K) x i)]
  rw [supportPlace_comap]
  simp [supportRationalPlace]

#check S2743_supportPlace_liesOver
#check S2743_supportPlace_under
#print axioms S2743_supportPlace_liesOver

end LeanFormal.IUT.XiFPaper.S2743LiesOverComapBridgeActual
end
