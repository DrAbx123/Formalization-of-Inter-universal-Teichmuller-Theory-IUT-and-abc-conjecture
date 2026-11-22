import tmp.sheaf.n8.closure.C1ActualDataC6
import tmp.sheaf.n8.closure.C10BridgeProof

/-! # Named C1 actual-data components

The remaining C1 gap packaged as C6ContractSupply + family index equivalence + a NativePlaceBindingDonors package on the resulting input. The binding carries the actual place equivalence, selected place, realization and fiber comparison, so C1ActualData and SourceInputBinding are constructed directly.

SEMANTIC NOTE: `contractSupply` only requires C6ContractSupply over the native arithmetic root; it does not force the contract to match the native tuple source selection. This is a weak contract-over-arithmetic interface, not the paper-level native contract. See coord/C1-SINGLETON-SEMANTICS.md. The canonical source-facing package is C1DonorCanonical.C1DonorPackage (P6BridgeDonors).
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.C6ConstructedBridge
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Named remaining C1 components. -/
structure C1ActualDataComponents (X : N8NativeInput l) where
  contractSupply : C6ContractSupply X
  indexEquiv : X.family.index ≃ SourceTheorem311Index
  binding : NativePlaceBindingDonors X (nativeC6Input X contractSupply indexEquiv)

/-- C1ActualData from the named components. -/
noncomputable def c1ActualDataOfComponents
    (D : C1ActualDataComponents X) :
    C1ActualData (nativeC6Input X D.contractSupply D.indexEquiv) where
  placeEquiv := D.binding.placeEquiv
  selected := D.binding.selected
  selected_realization := D.binding.selected_realization
  fiberMonEquiv := D.binding.fiberMonEquiv

theorem c1ActualData_nonempty_of_components
    (D : C1ActualDataComponents X) :
    Nonempty (C1ActualData (nativeC6Input X D.contractSupply D.indexEquiv)) :=
  ⟨c1ActualDataOfComponents X D⟩

theorem sourceInputBinding_nonempty_of_components
    (D : C1ActualDataComponents X) :
    Nonempty (SourceInputBinding (nativeC6Input X D.contractSupply D.indexEquiv)) :=
  ⟨sourceInputBindingOfActual (nativeC6Input X D.contractSupply D.indexEquiv)
    (c1ActualDataOfComponents X D)⟩

/-- Explicit-field constructor: selected badPlace and canonical placeEquiv. -/
noncomputable def C1ActualDataComponents.ofFields
    (h : C6ContractSupply X) (e : X.family.index ≃ SourceTheorem311Index)
    (R : (nativeC6Input X h e).SourceImageRealization (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeC6Input X h e).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := (nativeOriginalInputDonorsOf X h e).initial.arithmetic.Fmod)
          (((nativeOriginalInputDonorsOf X h e).initial_arithmetic ▸ nativePlaceIndexEquiv X) v)) :
    C1ActualDataComponents X where
  contractSupply := h
  indexEquiv := e
  binding := nativePlaceBindingDonorsOf X (nativeC6Input X h e)
    (nativeOriginalInputDonorsOf X h e).initial_arithmetic R F

/-- Direct constructor from an existing native binding package. -/
noncomputable def C1ActualDataComponents.ofBinding
    (h : C6ContractSupply X) (e : X.family.index ≃ SourceTheorem311Index)
    (P : NativePlaceBindingDonors X (nativeC6Input X h e)) :
    C1ActualDataComponents X where
  contractSupply := h
  indexEquiv := e
  binding := P

theorem c1ActualData_nonempty_ofBinding
    (h : C6ContractSupply X) (e : X.family.index ≃ SourceTheorem311Index)
    (P : NativePlaceBindingDonors X (nativeC6Input X h e)) :
    Nonempty (C1ActualData (nativeC6Input X h e)) :=
  c1ActualData_nonempty_of_components X (C1ActualDataComponents.ofBinding X h e P)

theorem sourceInputBinding_nonempty_ofBinding
    (h : C6ContractSupply X) (e : X.family.index ≃ SourceTheorem311Index)
    (P : NativePlaceBindingDonors X (nativeC6Input X h e)) :
    Nonempty (SourceInputBinding (nativeC6Input X h e)) :=
  sourceInputBinding_nonempty_of_components X (C1ActualDataComponents.ofBinding X h e P)

end LeanFormal.IUT.N8Closure.C1Actual
end