import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2688BadReductionSelectionActual

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{0} l}

/-- A source place selection whose bad moduli set is *tied* to actual
multiplicative reduction: every p in V_mod_bad has some F-place over it
with multiplicative reduction.  This is the missing field of
`SourcePlaceSelection`; it is not present in `SourcePlaceSelection.singleton`. -/
structure SourcePlaceSelectionWithMultiplicativeReduction
    (A : InitialThetaArithmeticData.{0} l)
    extends SourcePlaceSelection A where
  multiplicativeReduction :
    ∀ p ∈ V_mod_bad,
      ∃ w : NumberField.FinitePlace A.F,
        NumberFieldFinitePlace.comap (k := A.Fmod) w = p ∧
          A.curve.HasMultiplicativeReductionAt w

/-- The Fmod bad set cut out by actual multiplicative reduction at some
F-place over it. -/
def S2688BadFmodSet (l : PrimeGeFive) :
    Set (NumberField.FinitePlace (S1280Arithmetic l).Fmod) :=
  {p | ∃ w : NumberField.FinitePlace (S1280Arithmetic l).F,
    NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w = p ∧
      (S1280Arithmetic l).curve.HasMultiplicativeReductionAt w}

/-- The concrete place above 5 belongs to the actual bad set. -/
theorem S2688_five_mem_badSet :
    S1280Place l ∈ S2688BadFmodSet l := by
  refine ⟨S1280Place l, ?_, concreteGaussianFivePlace_hasMultiplicativeReduction l⟩
  rw [S1280_comap_eq_self]

/-- The expected second bad prime 2161 is *not* discharged here: this
records the exact missing actual arithmetic place/reduction. -/
def S2688HasBadPlace2161 (l : PrimeGeFive) : Prop :=
  ∃ p ∈ S2688BadFmodSet l,
    NumberFieldFinitePlace.residueCharacteristic p = 2161

#check SourcePlaceSelectionWithMultiplicativeReduction
#check S2688BadFmodSet
#check S2688_five_mem_badSet
#check S2688HasBadPlace2161
#print axioms S2688_five_mem_badSet

end LeanFormal.IUT.XiFPaper.S2688BadReductionSelectionActual
end