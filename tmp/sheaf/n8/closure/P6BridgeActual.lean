import tmp.sheaf.n8.closure.P6Bridge
import tmp.sheaf.n8.closure.C1BridgeProof

/-!
# P6BridgeActual: attempt at constructing P6BridgeDonors from native S/lattice

Actual partial data: native place/selected-place donors (NativeC1).
Missing: the contract datum/index equivalence and the old R/fiber donors.
No arbitrary V or selected R is introduced.

The full donor existence remains a theorem-level named sorry; a conditional
no-go is proved when no `SourceDefinition31Data` exists.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6BridgeActual

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C1BridgeProof
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- Actual native S/lattice place data, constructed without sorry. -/
structure P6ActualPartial (X : N8NativeInput l) where
  /-- Actual native place equivalence to finite/infinite places. -/
  placeEquiv : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod)
  /-- Actual selected native place. -/
  selected : NativePlaces X.S
  /-- Membership in the native selected-place set. -/
  selected_mem : selected.1 ∈ X.S.tuple.source.V
  /-- Its base place is the native bad base place. -/
  selected_comap :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) selected.1 =
      NumberFieldPlace.finite (badBasePlace X)

/-- Actual partial construction from NativeC1. -/
noncomputable def p6ActualPartial (X : N8NativeInput l) : P6ActualPartial X where
  placeEquiv := nativePlaceIndexEquiv X
  selected := badPlace X
  selected_mem := (badPlace X).2
  selected_comap := badPlace_comap X

/-- Exact missing contract datum (reused; no new object). -/
def P6ContractDatumMissing (X : N8NativeInput l) : Prop :=
  NativeContractDatumExists X

/-- Exact missing old R/fiber donors (reused; no new object). -/
def P6OldBindingMissing (X : N8NativeInput l) : Prop :=
  NativeOldBindingDonorsExist X

/-- Conditional exact no-go: an empty contract type rules out the P6 donor
package. -/
theorem no_p6BridgeDonors_of_empty_contract (X : N8NativeInput l)
    (h : IsEmpty (SourceDefinition31Data.{0} l)) :
    IsEmpty (P6BridgeDonors X) :=
  ⟨fun D => h.false D.inputDonors.initial⟩

end LeanFormal.IUT.N8Closure.P6BridgeActual