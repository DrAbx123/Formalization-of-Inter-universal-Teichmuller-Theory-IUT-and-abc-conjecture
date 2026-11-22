import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticPacketVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks

/-!
# An actual selected common-prime packet

Choose exactly one upper place over each lower place. The selected subset
of the upper prime fiber is genuinely equivalent to the lower full prime
fiber, and hence finite and nonempty. Its completion packet retains these
selected coordinates, rather than all upper places.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable (k K : Type*) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable (p : ℕ) [Fact p.Prime]

def SelectedCommonPrimePlaces :=
  Set.range (selectedCommonPrimePlace (k := k) (K := K) (p := p))

def selectedCommonPrimePlacesEquiv : FinitePlaceAtPrime k p ≃ SelectedCommonPrimePlaces k K p :=
  Equiv.ofInjective _ (selectedCommonPrimePlace_injective (k := k) (K := K) (p := p))

instance selectedCommonPrimePlacesFinite : Finite (SelectedCommonPrimePlaces k K p) :=
  Finite.of_equiv (FinitePlaceAtPrime k p) (selectedCommonPrimePlacesEquiv k K p)

instance selectedCommonPrimePlacesNonempty : Nonempty (SelectedCommonPrimePlaces k K p) :=
  ⟨selectedCommonPrimePlacesEquiv k K p
    (Classical.choice (inferInstance : Nonempty (FinitePlaceAtPrime k p)))⟩

abbrev SelectedPrimeCompletionPacket :=
  CompletionPacket (selectedCommonPrimePlace (k := k) (K := K) (p := p))

def selectedPrimeArithmeticPlaces (ι : Type*) :
    (i : ι) → FinitePlaceAtPrime k p → FinitePlaceAtPrime K p :=
  fun _ => selectedCommonPrimePlace

abbrev SelectedPrimeArithmeticTensor (ι : Type*) :=
  ArithmeticPacketTensor (selectedPrimeArithmeticPlaces k K p ι)

open Classical in
theorem fullPrimeArithmeticTensorDimension_eq_sum_tupleBlocks (ι : Type*) [Fintype ι] :
    fullPrimeArithmeticTensorDimension k p ι =
      ∑ tuple : ι → FinitePlaceAtPrime k p,
        Module.finrank ℚ_[p]
          (ArithmeticTensorTupleBlock (fullPrimeArithmeticPlaces k p ι) tuple) :=
  finrank_arithmeticPacketTensor_eq_sum_blocks (fullPrimeArithmeticPlaces k p ι)

end

end LeanFormal.IUT.NumberFieldFinitePlace
