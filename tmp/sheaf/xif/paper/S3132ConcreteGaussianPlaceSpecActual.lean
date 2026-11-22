import LeanFormal.IUT.IUTII.Frobenioid.Example36PacketNumberField
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PacketNumberFieldConstruction
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132ConcreteGaussianPlaceSpecActual

/-!
# task-65 follow-up: concrete Example 3.6 / Gaussian place data for the fiber instantiation

**Component, not a paper object.**  Owner: hull.  Consumers: task-65
`ActualPlaceDataForC3`; mainline registry.

The concrete Example 3.6 packet number field `packetNumberField = Q(i)` carries the
actual finite place `packetFinitePlace` over the rational place 5.  The tree
already proves the data needed by the fiber instantiation spec:

* **rational place / prime:** `packetFinitePlace_natGenerator` — the rational
  prime below `packetFinitePlace` has natural generator 5
  (`packet_rationalPrime_eq_five`); `packetFinitePlace_comap` identifies the
  rational place with the concrete five-place;
* **local degree one (e = f = 1):**
  `packet_relativeCompletionDegree_eq_one` and
  `packet_completion_finrank_eq_one` (transported from
  `concreteGaussianFivePlace_relativeCompletionDegree_eq_one` /
  `concreteGaussianFivePlace_completion_finrank_eq_one`: both primes of Z[i]
  over 5 have e = f = 1);
* **injectivity:** `packet_completionMap_injective`
  (`completionMap_injective`, LeanFormal Foundations);
* **source-theater tie:** `sourceTheater_Fmod_eq_packet` shows the concrete
  source theater's `Fmod` is the packet number field.

**Conditional concrete fiber equivalence.**
`concreteGaussianFiberRingEquiv_of_surjective`: if the rational-to-packet
completion map is surjective (bijective, given injectivity), the concrete fiber
ring equivalence exists.  Together with the degree-one fact, the single remaining
manufactured step is the dimension/rank-nullity argument (injective + finrank one
=> surjective), requiring the module-structure alignment noted in the plan.

**ABSENT (exact model-specific data):** no concrete `OriginalInput` /
`SourcePilotRegionData` instantiation is available whose selected C3 tensor
places `c3LogShellPlace C3 i` are these concrete packet places, so
`ActualPlaceDataForC3` cannot yet be instantiated for the model.  Residual model
data: (i) place identification `c3LogShellPlace C3 i = packetFinitePlace` for a
concrete C3 (from the source theater data), (ii) the surjectivity above.
Pages: IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.7, (ii), (v),
pp. 108-112.
-/

/-- The rational prime below the concrete packet place is 5. -/
theorem packet_rationalPrime_eq_five :
    Rat.HeightOneSpectrum.natGenerator
      (NumberFieldFinitePlace.underlyingPrime
        (NumberFieldFinitePlace.comap (k := ℚ) packetFinitePlace)) = 5 :=
  packetFinitePlace_natGenerator

/-- The concrete packet place has relative completion degree one (e = f = 1). -/
theorem packet_relativeCompletionDegree_eq_one :
    relativeCompletionDegree (k := ℚ) packetFinitePlace = 1 := by
  rw [packetFinitePlace_eq_concreteGaussianFivePlace]
  exact concreteGaussianFivePlace_relativeCompletionDegree_eq_one

/-- The local completion degree of the concrete packet place over Q_5 is one. -/
theorem packet_completion_finrank_eq_one :
    Module.finrank
      ((NumberFieldFinitePlace.comap (k := ℚ) packetFinitePlace).maximalIdeal.adicCompletion ℚ)
      (packetFinitePlace.maximalIdeal.adicCompletion packetNumberField) = 1 := by
  rw [packetFinitePlace_eq_concreteGaussianFivePlace]
  exact concreteGaussianFivePlace_completion_finrank_eq_one

/-- The rational-to-packet completion map is injective. -/
theorem packet_completionMap_injective :
    Function.Injective (completionMap (k := ℚ) packetFinitePlace) :=
  completionMap_injective (k := ℚ) packetFinitePlace

/-- The concrete source theater's `Fmod` is the packet number field. -/
theorem sourceTheater_Fmod_eq_packet (l : PrimeGeFive) :
    (SourceTheaterCarrier.sourceTheater l).arithmetic.Fmod = packetNumberField :=
  sourceTheater_arithmetic_Fmod_eq_packet l

/-- **Data-instantiation spec for the concrete Example 3.6 model** (all fields
proved). -/
structure ConcreteGaussianFiberDataSpec : Prop where
  rationalPrime_eq_five :
    Rat.HeightOneSpectrum.natGenerator
      (NumberFieldFinitePlace.underlyingPrime
        (NumberFieldFinitePlace.comap (k := ℚ) packetFinitePlace)) = 5
  degree_one : relativeCompletionDegree (k := ℚ) packetFinitePlace = 1
  local_finrank_one :
    Module.finrank
      ((NumberFieldFinitePlace.comap (k := ℚ) packetFinitePlace).maximalIdeal.adicCompletion ℚ)
      (packetFinitePlace.maximalIdeal.adicCompletion packetNumberField) = 1
  completionMap_injective : Function.Injective (completionMap (k := ℚ) packetFinitePlace)
  sourceTheater_Fmod : ∀ l : PrimeGeFive,
    (SourceTheaterCarrier.sourceTheater l).arithmetic.Fmod = packetNumberField

/-- The concrete data spec holds. -/
theorem concreteGaussianFiberDataSpec_holds : ConcreteGaussianFiberDataSpec :=
  { rationalPrime_eq_five := packet_rationalPrime_eq_five
    degree_one := packet_relativeCompletionDegree_eq_one
    local_finrank_one := packet_completion_finrank_eq_one
    completionMap_injective := packet_completionMap_injective
    sourceTheater_Fmod := sourceTheater_Fmod_eq_packet }

/-- **Conditional concrete fiber equivalence:** if the rational-to-packet
completion map is surjective (bijective, given injectivity), the concrete fiber
ring equivalence exists. -/
theorem concreteGaussianFiberRingEquiv_of_surjective
    (hsurj : Function.Surjective (completionMap (k := ℚ) packetFinitePlace)) :
    Nonempty
      (Completion (NumberFieldFinitePlace.comap (k := ℚ) packetFinitePlace) ≃+*
        packetFiniteCompletion) := by
  have hbij : Function.Bijective (completionMap (k := ℚ) packetFinitePlace) :=
    ⟨packet_completionMap_injective, hsurj⟩
  exact ⟨RingEquiv.ofBijective (completionMap (k := ℚ) packetFinitePlace) hbij⟩

#check packet_rationalPrime_eq_five
#check packet_relativeCompletionDegree_eq_one
#check packet_completion_finrank_eq_one
#check packet_completionMap_injective
#check sourceTheater_Fmod_eq_packet
#check concreteGaussianFiberDataSpec_holds
#check concreteGaussianFiberRingEquiv_of_surjective

end LeanFormal.IUT.XiFPaper.S3132ConcreteGaussianPlaceSpecActual

end
