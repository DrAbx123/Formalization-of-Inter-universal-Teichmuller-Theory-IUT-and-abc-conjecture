import tmp.sheaf.n8.closure.P6Bridge
import tmp.sheaf.n8.closure.C1BridgeProof
import tmp.sheaf.n8.closure.C10BridgeProof

/-!
# C6 constructed bridge

Constructs the actual native place fields of the C6 bridge:

- placeEquiv : NativePlaces X.S ~ NumberFieldPlaceIndex, from NativeC1;
- selected = badPlace X, with actual membership and base-place identification.

It does NOT invent a selected realization R or a fiberMonEquiv.  The remaining
input/binding donors are precise parameters:

- C6ContractSupply X: a contract datum with the native arithmetic root;
- indexEquiv : X.family.index ~ SourceTheorem311Index;
- R : I.SourceImageRealization (badPlace X);
- fiberMonEquiv over the actual native place equivalence.

Given those exact fields, the file constructs NativeOriginalInputDonors,
NativePlaceBindingDonors and P6BridgeDonors without any arbitrary choice.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C6ConstructedBridge

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.C1BridgeProof
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- Actual native place fields of the C6 bridge, constructed from NativeC1. -/
structure C6ActualPlaceFields (X : N8NativeInput l) where
  placeEquiv : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod)
  selected : NativePlaces X.S
  selected_mem : selected.1 ∈ X.S.tuple.source.V
  selected_comap :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) selected.1 =
      NumberFieldPlace.finite (badBasePlace X)

/-- Actual construction from NativeC1; zero arbitrary fields. -/
noncomputable def c6ActualPlaceFields (X : N8NativeInput l) : C6ActualPlaceFields X where
  placeEquiv := nativePlaceIndexEquiv X
  selected := badPlace X
  selected_mem := (badPlace X).2
  selected_comap := badPlace_comap X

/-- Precise missing input donor: contract datum over the native arithmetic root. -/
def C6ContractSupply (X : N8NativeInput l) : Prop :=
  ∃ initial : SourceDefinition31Data.{0} l, initial.arithmetic = X.S.arithmetic

/-- Precise missing input donor: family index equivalence. -/
def C6IndexSupply (X : N8NativeInput l) : Prop :=
  Nonempty (X.family.index ≃ SourceTheorem311Index)

/-- Exact remaining input-donor dependency, with no arbitrary datum. -/
def C6InputDonorsMissing (X : N8NativeInput l) : Prop :=
  C6ContractSupply X ∧ C6IndexSupply X

/-- Actual NativeOriginalInputDonors from supplied contract and index data. -/
noncomputable def nativeOriginalInputDonorsOf
    (X : N8NativeInput l) (h : C6ContractSupply X)
    (e : X.family.index ≃ SourceTheorem311Index) :
    NativeOriginalInputDonors X where
  initial := Classical.choose h
  initial_arithmetic := Classical.choose_spec h
  index_equiv := e

/-- Actual NativePlaceBindingDonors fields from the native place data and the
two supplied old-binding donors R and fiberMonEquiv. -/
noncomputable def nativePlaceBindingDonorsOf
    (X : N8NativeInput l) (I : OriginalInput l (NativePlaces X.S))
    (hI : I.initial.arithmetic = X.S.arithmetic)
    (R : I.SourceImageRealization (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      (I.primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod)
          ((hI ▸ nativePlaceIndexEquiv X) v)) :
    NativePlaceBindingDonors X I where
  placeEquiv := hI ▸ nativePlaceIndexEquiv X
  selected := badPlace X
  selected_realization := R
  fiberMonEquiv := F

/-- Precise remaining binding-donor dependency for an input I: selected R and
fiberMonEquiv are not constructed by NativeC1. -/
def C6BindingDonorsMissing
    (X : N8NativeInput l) (I : OriginalInput l (NativePlaces X.S)) : Prop :=
  Nonempty (NativePlaceBindingDonors X I)

/-- Construct P6BridgeDonors from the actual native place fields and the exact
supplied input/binding donors. -/
noncomputable def c6BridgeDonorsOf
    (X : N8NativeInput l) (h : C6ContractSupply X)
    (e : X.family.index ≃ SourceTheorem311Index)
    (R : (nativeOriginalInputOfDonors X (nativeOriginalInputDonorsOf X h e)).SourceImageRealization
      (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeOriginalInputOfDonors X (nativeOriginalInputDonorsOf X h e)).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup
          (F := (nativeOriginalInputDonorsOf X h e).initial.arithmetic.Fmod)
          (((nativeOriginalInputDonorsOf X h e).initial_arithmetic ▸ nativePlaceIndexEquiv X) v)) :
    P6BridgeDonors X :=
  let D := nativeOriginalInputDonorsOf X h e
  { inputDonors := D
    bindingDonors := nativePlaceBindingDonorsOf X
      (nativeOriginalInputOfDonors X D) D.initial_arithmetic R F }

/-- The exact C6 donor target: input donors plus a nonempty binding package. -/
def C6BridgeDonorsTarget (X : N8NativeInput l) : Prop :=
  ∃ D : NativeOriginalInputDonors X,
    Nonempty (NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D))

/-- Actual construction of the target from the explicit precise fields. -/
theorem c6BridgeDonorsTarget_of_fields
    (X : N8NativeInput l) (h : C6ContractSupply X)
    (e : X.family.index ≃ SourceTheorem311Index)
    (P : NativePlaceBindingDonors X
      (nativeOriginalInputOfDonors X (nativeOriginalInputDonorsOf X h e))) :
    C6BridgeDonorsTarget X :=
  ⟨nativeOriginalInputDonorsOf X h e, ⟨P⟩⟩

/-- Actual P6 donor package from the target and the explicit fields. -/
theorem p6BridgeDonors_of_target_and_binding
    (X : N8NativeInput l) (h : C6ContractSupply X)
    (e : X.family.index ≃ SourceTheorem311Index)
    (P : NativePlaceBindingDonors X
      (nativeOriginalInputOfDonors X (nativeOriginalInputDonorsOf X h e))) :
    P6BridgeDonorsExist X :=
  ⟨{ inputDonors := nativeOriginalInputDonorsOf X h e
     bindingDonors := P }⟩

end LeanFormal.IUT.N8Closure.C6ConstructedBridge
