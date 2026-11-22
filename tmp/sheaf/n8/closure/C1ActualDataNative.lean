import tmp.sheaf.n8.closure.C1Actual
import tmp.sheaf.n8.closure.C10BridgeProof
import tmp.sheaf.n8.closure.C1SourceInputBindingEquiv

/-! # Actual C1 data from the native donors

For the native input carrier `V = NativePlaces X.S`, the old `OriginalInput`
`nativeOriginalInputOfDonors X D` and the exact `NativePlaceBindingDonors X I`
have precisely the four fields of `C1ActualData I`. This file constructs
`C1ActualData` and the corresponding `SourceInputBinding` from those donors.
The donors themselves are not constructed; no fake data is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive}

/-- Actual C1 data for the native old input from the two donor packages. -/
noncomputable def c1ActualDataOfNativeDonors
    (X : N8NativeInput l) (D : NativeOriginalInputDonors X)
    (P : NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D)) :
    C1ActualData (nativeOriginalInputOfDonors X D) where
  placeEquiv := P.placeEquiv
  selected := P.selected
  selected_realization := P.selected_realization
  fiberMonEquiv := P.fiberMonEquiv

/-- The native donors give an actual SourceInputBinding. -/
noncomputable def sourceInputBindingOfNativeDonors
    (X : N8NativeInput l) (D : NativeOriginalInputDonors X)
    (P : NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D)) :
    SourceInputBinding (nativeOriginalInputOfDonors X D) :=
  sourceInputBindingOfActual (nativeOriginalInputOfDonors X D)
    (c1ActualDataOfNativeDonors X D P)

theorem sourceInputBinding_nonempty_of_nativeDonors
    (X : N8NativeInput l) (D : NativeOriginalInputDonors X)
    (P : NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D)) :
    Nonempty (SourceInputBinding (nativeOriginalInputOfDonors X D)) :=
  ⟨sourceInputBindingOfNativeDonors X D P⟩

end LeanFormal.IUT.N8Closure.C1Actual