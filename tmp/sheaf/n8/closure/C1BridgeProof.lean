import tmp.sheaf.n8.closure.C10BridgeProof
import tmp.sheaf.n8.closure.NativeC1

/-!
# C1-BRIDGE: actual native parts + reduced exact donor gaps

`NativeOldC1Bridge X` needs `OriginalInput l (NativePlaces X.S)` and an old
`SourceInputBinding`.  This file:
1. constructs the actual native place/selected-place donors from NativeC1;
2. reuses the exact conditional donor interfaces and constructor from
   `C10BridgeProof` (no arbitrary V, no arbitrary selected R);
3. records the two exact missing production donors as named-sorry theorems:
   `SourceDefinition31Data` over the native arithmetic root, and the old
   `SourceImageRealization`/fiber donors.

No unconditional no-go for `SourceDefinition31Data` is provable from the
current tree: the boundary has only dependent/existential bridge gates and a
`StageConstructionTrace` constructor, not a native -> contract function.  The
conditional empty-contract no-go is included below.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1BridgeProof

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- Actual place donor: NativeC1 place equivalence to the finite/infinite index. -/
noncomputable def nativePlaceEquivDonor (X : N8NativeInput l) :
    NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod) :=
  nativePlaceIndexEquiv X

/-- Actual selected-place donor: the native bad place. -/
noncomputable def nativeSelectedPlaceDonor (X : N8NativeInput l) : NativePlaces X.S :=
  badPlace X

theorem nativeSelectedPlaceDonor_mem (X : N8NativeInput l) :
    (nativeSelectedPlaceDonor X).1 ∈ X.S.tuple.source.V :=
  (badPlace X).2

theorem nativeSelectedPlaceDonor_comap (X : N8NativeInput l) :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) (nativeSelectedPlaceDonor X).1 =
      NumberFieldPlace.finite (badBasePlace X) :=
  badPlace_comap X

/-- Actual native C1 parts, all constructed from NativeC1 (zero sorry). -/
structure NativeC1ActualParts (X : N8NativeInput l) where
  placeEquiv : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod)
  selected : NativePlaces X.S
  selected_mem : selected.1 ∈ X.S.tuple.source.V
  selected_comap :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) selected.1 =
      NumberFieldPlace.finite (badBasePlace X)

noncomputable def nativeC1ActualParts (X : N8NativeInput l) : NativeC1ActualParts X where
  placeEquiv := nativePlaceEquivDonor X
  selected := nativeSelectedPlaceDonor X
  selected_mem := nativeSelectedPlaceDonor_mem X
  selected_comap := nativeSelectedPlaceDonor_comap X

/-- Exact missing production donor: a contract datum over the native arithmetic
root.  No native -> `SourceDefinition31Data` constructor exists in production. -/
def NativeContractDatumExists (X : N8NativeInput l) : Prop :=
  ∃ initial : SourceDefinition31Data.{0} l, initial.arithmetic = X.S.arithmetic

/-- Exact missing production donor: the old `SourceImageRealization`/fiber
binding over an `OriginalInput` built from the contract donor. -/
def NativeOldBindingDonorsExist (X : N8NativeInput l) : Prop :=
  ∃ D : NativeOriginalInputDonors X,
    Nonempty (NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D))

/-- Conditional bridge construction from the exact donor packages. -/
noncomputable def nativeOldC1Bridge_of_donors
    (X : N8NativeInput l) (D : NativeOriginalInputDonors X)
    (P : NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D)) :
    NativeOldC1Bridge X :=
  C10BridgeProof.nativeOldC1Bridge_of_donors X D P

/-- Conditional exact no-go: an empty `SourceDefinition31Data` type rules out
the native old bridge. -/
theorem no_nativeOldC1Bridge_of_empty_contract
    (X : N8NativeInput l) (h : IsEmpty (SourceDefinition31Data.{0} l)) :
    IsEmpty (NativeOldC1Bridge X) :=
  C10BridgeProof.no_nativeOldC1Bridge_of_empty_contract X h

end LeanFormal.IUT.N8Closure.C1BridgeProof