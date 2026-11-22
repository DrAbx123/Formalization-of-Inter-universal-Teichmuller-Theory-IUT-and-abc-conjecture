import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.Foundations.Geometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2701FivePlacesActual

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

abbrev O := NumberField.RingOfIntegers GaussianField

noncomputable def S2701HeightPlus :
    IsDedekindDomain.HeightOneSpectrum O where
  asIdeal := gaussianFieldFivePrimePlus
  isPrime := gaussianFieldFivePrimePlus_isMaximal.isPrime
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
    gaussianFieldFivePrimePlus_isMaximal
    (NumberField.RingOfIntegers.not_isField GaussianField)

noncomputable def S2701HeightMinus :
    IsDedekindDomain.HeightOneSpectrum O where
  asIdeal := gaussianFieldFivePrimeMinus
  isPrime := gaussianFieldFivePrimeMinus_isMaximal.isPrime
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
    gaussianFieldFivePrimeMinus_isMaximal
    (NumberField.RingOfIntegers.not_isField GaussianField)

def S2701PlacePlus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk S2701HeightPlus
def S2701PlaceMinus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk S2701HeightMinus

def S2701PiPlus : O := gaussianRingOfIntegersEquivGaussianInt.symm gaussianIntFiveGenerator
def S2701PiMinus : O := gaussianRingOfIntegersEquivGaussianInt.symm gaussianIntFiveConjugate

theorem S2701PiPlus_ne_zero : S2701PiPlus ≠ 0 := by
  intro h
  have hgen : gaussianIntFiveGenerator = 0 := by
    have := congrArg gaussianRingOfIntegersEquivGaussianInt h
    simpa [S2701PiPlus] using this
  have hnorm : Zsqrtd.norm gaussianIntFiveGenerator = 5 := gaussianIntFiveGenerator_norm
  rw [hgen] at hnorm
  simp at hnorm

theorem S2701PiMinus_ne_zero : S2701PiMinus ≠ 0 := by
  intro h
  have hgen : gaussianIntFiveConjugate = 0 := by
    have := congrArg gaussianRingOfIntegersEquivGaussianInt h
    simpa [S2701PiMinus] using this
  have hnorm : Zsqrtd.norm gaussianIntFiveConjugate = 5 := gaussianIntFiveConjugate_norm
  rw [hgen] at hnorm
  simp at hnorm

theorem S2701PiPlus_mem : S2701PiPlus ∈ gaussianFieldFivePrimePlus := by
  rw [gaussianFieldFivePrimePlus, Ideal.mem_comap]
  change gaussianRingOfIntegersEquivGaussianInt (S2701PiPlus) ∈
    Ideal.span {gaussianIntFiveGenerator}
  simp [S2701PiPlus]

theorem S2701PiMinus_mem : S2701PiMinus ∈ gaussianFieldFivePrimeMinus := by
  rw [gaussianFieldFivePrimeMinus, Ideal.mem_comap]
  change gaussianRingOfIntegersEquivGaussianInt (S2701PiMinus) ∈
    Ideal.span {gaussianIntFiveConjugate}
  simp [S2701PiMinus]

theorem S2701_valuation_lt_one_of_mem
    (place : NumberField.FinitePlace GaussianField) {π : O}
    (hmem : π ∈ place.maximalIdeal.asIdeal) :
    (Valued.v (algebraMap O (Completion place) π) :
      WithZero (Multiplicative Int)) < 1 := by
  have hfield : (underlyingPrime (K := GaussianField) place).valuation GaussianField
      (algebraMap O GaussianField π) < 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (K := GaussianField) (v := underlyingPrime (K := GaussianField) place) π).mpr hmem
  rw [← valued_algebraMap_completionIntegers place π]
  exact hfield

noncomputable def S2701QPlus : FinitePlaceQCandidate S2701PlacePlus :=
  { q := algebraMap O (Completion S2701PlacePlus) S2701PiPlus
    q_ne_zero := by
      intro h
      have hK : algebraMap O GaussianField S2701PiPlus = 0 := by
        apply algebraMap_completion_injective (K := GaussianField) S2701PlacePlus
        simpa [IsScalarTower.algebraMap_apply] using h
      exact S2701PiPlus_ne_zero ((NumberField.RingOfIntegers.coe_injective (K := GaussianField)) hK)
    valuation_lt_one := by
      apply S2701_valuation_lt_one_of_mem
      change S2701PiPlus ∈ gaussianFieldFivePrimePlus
      exact S2701PiPlus_mem }

noncomputable def S2701QMinus : FinitePlaceQCandidate S2701PlaceMinus :=
  { q := algebraMap O (Completion S2701PlaceMinus) S2701PiMinus
    q_ne_zero := by
      intro h
      have hK : algebraMap O GaussianField S2701PiMinus = 0 := by
        apply algebraMap_completion_injective (K := GaussianField) S2701PlaceMinus
        simpa [IsScalarTower.algebraMap_apply] using h
      exact S2701PiMinus_ne_zero ((NumberField.RingOfIntegers.coe_injective (K := GaussianField)) hK)
    valuation_lt_one := by
      apply S2701_valuation_lt_one_of_mem
      change S2701PiMinus ∈ gaussianFieldFivePrimeMinus
      exact S2701PiMinus_mem }

#check S2701PlacePlus
#check S2701PlaceMinus
#check S2701QPlus
#check S2701QMinus
#print axioms S2701QPlus
#print axioms S2701QMinus

end LeanFormal.IUT.XiFPaper.S2701FivePlacesActual
end