import tmp.sheaf.xif.paper.ConcreteC3DonorCompletionActual
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteIntegralHodgeTheaterExample

/-!
# Concrete C3 place-tensor witness

ConcreteC3DonorCompletionActual supplies actual concrete tensor data:

  tensorIndex = FinitePrimePlace 2 7,
  tensorPlaceIndex = fun _ => Unit,
  tensorPlaces i () = place,
  tensorTuple i = ().

This file constructs the actual concrete place-tensor witness: the index
fiveFinitePrimePlace, the unique tensor place index, and the definitional
equality concreteTensorPlaces i () = place.  This is the concrete/rfl version of
C3PlaceTensorWitness, not an empty obstruction and not a fake tensor embedding.

The general C3PlaceTensorWitness for an arbitrary SourcePilotRegionData still
requires its own place equality; the concrete data supplies it here.

No True/PUnit/axiom/sorry and no inequality.  WRITE-ONLY; no local compile;
queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.C3PlaceTensorWitnessActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorCompletionActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The actual concrete C3 place-tensor witness. -/
structure ConcreteC3PlaceTensorWitness where
  i : ConcreteTensorIndex
  a : ConcreteTensorPlaceIndex i
  place_eq : concreteTensorPlaces I place i a = place

/-- The actual witness at the concrete five place and the unique tensor index. -/
noncomputable def concreteC3PlaceTensorWitness :
    ConcreteC3PlaceTensorWitness I place where
  i := fiveFinitePrimePlace
  a := ()
  place_eq := rfl

/-- The witness's tensor place is exactly the supplied concrete place. -/
theorem concreteC3PlaceTensorWitness_place_eq :
    concreteTensorPlaces I place
      (concreteC3PlaceTensorWitness I place).i
      (concreteC3PlaceTensorWitness I place).a = place := rfl

/-- The witness's tensor tuple is the actual concrete tuple at its index. -/
theorem concreteC3PlaceTensorWitness_tuple_eq :
    (concreteC3PlaceTensorWitness I place).a =
      concreteTensorTuple I (concreteC3PlaceTensorWitness I place).i := rfl

/-- The actual concrete place-tensor witness target is inhabited. -/
theorem concreteC3PlaceTensorWitness_nonempty :
    Nonempty (ConcreteC3PlaceTensorWitness I place) :=
  ⟨concreteC3PlaceTensorWitness I place⟩

/-- The concrete witness uses the actual five finite prime place. -/
theorem concreteC3PlaceTensorWitness_index :
    (concreteC3PlaceTensorWitness I place).i = fiveFinitePrimePlace := rfl

end LeanFormal.IUT.XiFPaper.C3PlaceTensorWitnessActualAdapted
