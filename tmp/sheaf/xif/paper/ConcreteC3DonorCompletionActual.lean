import tmp.sheaf.xif.paper.ConcreteC3DonorActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks

/-! # Completion of concrete C3 donor fields

This file extends ConcreteC3DonorActual with the actual tensor-block data that
can be built from the concrete finite-place data:

* tensorIndex = FinitePrimePlace 2 7 (the actual concrete index type);
* tensorPlaceIndex = fun _ => Unit;
* tensorPlaces = constant actual finite place;
* tensorTuple = constant point;
* tensorUnit = the unit 1 of the actual ArithmeticTensorTupleBlock.

The root systems, Kummer class/root-change towers, and tensor landing are not
constructible from the concrete data: roots require the algebraic closure of the
completion, while candidateUnits lives in the completion; and tensorLanding is a
completion-to-tensor-block map not present.  Those are recorded as exact target
types/Obstruction propositions, not fabricated donors.  No inequality/True/toy/
axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.ConcreteC3DonorCompletionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The actual concrete tensor index: the finite prime places 2,...,7. -/
abbrev ConcreteTensorIndex : Type := FinitePrimePlace 2 7

/-- The actual tensor place index over the concrete tensor index. -/
abbrev ConcreteTensorPlaceIndex : ConcreteTensorIndex → Type := fun _ => Unit

/-- The actual tensor places: the constant supplied finite place. -/
noncomputable def concreteTensorPlaces
    (i : ConcreteTensorIndex) (j : ConcreteTensorPlaceIndex i) :
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p :=
  place

/-- The actual tensor tuple: the unique point in each place index. -/
noncomputable def concreteTensorTuple (i : ConcreteTensorIndex) :
    ConcreteTensorPlaceIndex i :=
  ()

/-- The actual arithmetic tensor block at the concrete tensor tuple. -/
abbrev ConcreteTensorBlock : Type ua :=
  ArithmeticTensorTupleBlock (concreteTensorPlaces I place) concreteTensorTuple

/-- The actual tensor unit: the multiplicative unit of the tensor block. -/
noncomputable def concreteTensorUnit : (ConcreteTensorBlock I place)ˣ :=
  (1 : (ConcreteTensorBlock I place)ˣ)

/-- The actual tensor unit is the unit 1 of the actual tensor block. -/
theorem concreteTensorUnit_val :
    (concreteTensorUnit I place : ConcreteTensorBlock I place) = 1 := rfl

/-- Exact missing tensor-landing target: a completion-to-tensor-block map taking
the actual q to the tensor unit. -/
structure ConcreteTensorLandingTarget where
  landing : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place →
    ConcreteTensorBlock I place
  landing_q : landing (Classical.choice
      (finitePlaceQCandidate_nonempty place.val)).q =
    concreteTensorUnit I place

/-- Exact tensor-landing obstruction for the concrete donor. -/
def ConcreteTensorLandingObstruction : Prop :=
  Nonempty (ConcreteTensorLandingTarget I place)

/-- Root-system target type for the first root system. -/
def ConcreteRootTarget : Type ua :=
  NatRootSystem (candidateUnits (K := I.initial.arithmetic.Fmod) place
    (Classical.choice (finitePlaceQCandidate_nonempty place.val)))

/-- Exact obstruction: no root system of the completion q unit is constructed. -/
def ConcreteRootObstruction : Prop := Nonempty (ConcreteRootTarget I place)

/-- Root-system target type for the second root system. -/
abbrev ConcreteRootPrimeTarget : Type ua := ConcreteRootTarget I place

/-- Exact obstruction for roots'. -/
def ConcreteRootPrimeObstruction : Prop := Nonempty (ConcreteRootPrimeTarget I place)

/-- Actual concrete tensor data that can be constructed. -/
structure ConcreteC3TensorActual where
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ

/-- The actual concrete tensor data from the concrete index and finite place. -/
noncomputable def concreteC3TensorActual : ConcreteC3TensorActual (I := I) (p := p) where
  tensorIndex := ConcreteTensorIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcreteTensorPlaceIndex
  tensorPlaces := concreteTensorPlaces I place
  tensorTuple := concreteTensorTuple
  tensorUnit := concreteTensorUnit I place

/-- The constructed tensor index is the actual finite prime place type. -/
theorem concreteC3TensorActual_index :
    (concreteC3TensorActual (I := I) (p := p) place).tensorIndex = ConcreteTensorIndex := rfl

/-- The constructed tensor unit is the unit 1 of the actual tensor block. -/
theorem concreteC3TensorActual_tensorUnit :
    ((concreteC3TensorActual (I := I) (p := p) place).tensorUnit :
      ArithmeticTensorTupleBlock
        (concreteC3TensorActual (I := I) (p := p) place).tensorPlaces
        (concreteC3TensorActual (I := I) (p := p) place).tensorTuple) = 1 := rfl

end LeanFormal.IUT.Theorem311Source.ConcreteC3DonorCompletionActual

end
