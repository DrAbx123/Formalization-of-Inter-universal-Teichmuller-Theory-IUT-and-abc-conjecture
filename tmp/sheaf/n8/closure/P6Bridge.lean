import tmp.sheaf.n8.closure.C1BridgeProof

/-!
# P6 bridge: native S/L -> old OriginalInput / C1 exact donors

Reuses `C1BridgeProof.NativeOriginalInputDonors` and
`NativePlaceBindingDonors`; does not recreate any old-layer object.

The exact source donor package is `P6BridgeDonors X`: a contract datum over
the native arithmetic root, its index equivalence to `SourceTheorem311Index`,
and the old place/R/fiber binding.  `P6BridgeDonors.toNativeOldC1Bridge`
builds the old bridge conditionally, with no arbitrary V or selected R.

Missing donor is the single theorem-level named sorry `p6BridgeDonorsExist`.
It is not a full `NativeOldC1Bridge` existence assertion.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6Bridge

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.C1BridgeProof
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- Native S/L entry used by P6 (actual native initial data plus lattice). -/
abbrev P6SL (l : PrimeGeFive) := N8NativeInput l

/-- The old OriginalInput type over the native place index. -/
abbrev P6OldOriginalInput {l : PrimeGeFive} (X : N8NativeInput l) :=
  OriginalInput l (NativePlaces X.S)

/-- The old C1 binding type for that input. -/
abbrev P6OldC1 {l : PrimeGeFive} {X : N8NativeInput l}
    (I : P6OldOriginalInput X) :=
  SourceInputBinding I

/-- Exact P6 source donor package for the native -> old bridge.
Both fields are existing C1BridgeProof donor structures; no new object is
invented. -/
structure P6BridgeDonors {l : PrimeGeFive} (X : N8NativeInput l) where
  /-- Contract datum + index equivalence over the native arithmetic root. -/
  inputDonors : NativeOriginalInputDonors X
  /-- Old place/selected/R/fiber binding for the resulting OriginalInput. -/
  bindingDonors : NativePlaceBindingDonors X
    (nativeOriginalInputOfDonors X inputDonors)

/-- Conditional exact bridge from the donor package. -/
noncomputable def P6BridgeDonors.toNativeOldC1Bridge
    {l : PrimeGeFive} {X : N8NativeInput l} (D : P6BridgeDonors X) :
    NativeOldC1Bridge X :=
  C10BridgeProof.nativeOldC1Bridge_of_donors X D.inputDonors D.bindingDonors

/-- Existence of the exact donor package (not of the full bridge). -/
def P6BridgeDonorsExist {l : PrimeGeFive} (X : N8NativeInput l) : Prop :=
  Nonempty (P6BridgeDonors X)

/-- The single exact named-sorry donor obligation. -/
theorem p6BridgeDonorsExist {l : PrimeGeFive} (X : N8NativeInput l) :
    P6BridgeDonorsExist X := by
  sorry

/-- Actual native place donor (reused from C1BridgeProof). -/
noncomputable def p6PlaceEquivDonor {l : PrimeGeFive} (X : N8NativeInput l) :
    NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod) :=
  nativePlaceEquivDonor X

/-- Actual native selected-place donor (reused from C1BridgeProof). -/
noncomputable def p6SelectedPlaceDonor {l : PrimeGeFive} (X : N8NativeInput l) :
    NativePlaces X.S :=
  nativeSelectedPlaceDonor X

/-- The exact conditional bridge from explicit donors. -/
noncomputable def p6NativeOldC1BridgeOfDonors {l : PrimeGeFive}
    (X : N8NativeInput l) (D : NativeOriginalInputDonors X)
    (P : NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D)) :
    NativeOldC1Bridge X :=
  C10BridgeProof.nativeOldC1Bridge_of_donors X D P

end LeanFormal.IUT.N8Closure.P6Bridge