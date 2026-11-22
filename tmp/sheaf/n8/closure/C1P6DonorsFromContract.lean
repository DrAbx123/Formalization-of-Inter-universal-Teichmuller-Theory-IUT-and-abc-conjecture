import tmp.sheaf.n8.closure.C1FromP6Donors
import tmp.sheaf.n8.closure.C6ContractSupplyOld
import tmp.sheaf.n8.closure.C6ConstructedBridge

/-! # P6/C1 donors from contract + index + R/F

NativeContractDatumExists, an index equivalence, a selected realization and a canonical fiber comparison construct P6BridgeDonors, hence NativeOldBindingDonorsExist and C1 actual data.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.C1BridgeProof
open LeanFormal.IUT.N8Closure.C6ConstructedBridge
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive} (X : N8NativeInput l)

noncomputable def p6BridgeDonors_of_contract
    (h : NativeContractDatumExists X)
    (e : X.family.index ≃ SourceTheorem311Index)
    (R : (nativeOriginalInputOfDonors X
      (nativeOriginalInputDonors_of_contract X h e)).SourceImageRealization (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeOriginalInputOfDonors X (nativeOriginalInputDonors_of_contract X h e)).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup
          (F := (nativeOriginalInputDonors_of_contract X h e).initial.arithmetic.Fmod)
          (((nativeOriginalInputDonors_of_contract X h e).initial_arithmetic ▸
            nativePlaceIndexEquiv X) v)) : P6BridgeDonors X where
  inputDonors := nativeOriginalInputDonors_of_contract X h e
  bindingDonors := nativePlaceBindingDonorsOf X
    (nativeOriginalInputOfDonors X (nativeOriginalInputDonors_of_contract X h e))
    (nativeOriginalInputDonors_of_contract X h e).initial_arithmetic R F

theorem nativeOldBindingDonorsExist_of_contract
    (h : NativeContractDatumExists X)
    (e : X.family.index ≃ SourceTheorem311Index)
    (R : (nativeOriginalInputOfDonors X
      (nativeOriginalInputDonors_of_contract X h e)).SourceImageRealization (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeOriginalInputOfDonors X (nativeOriginalInputDonors_of_contract X h e)).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup
          (F := (nativeOriginalInputDonors_of_contract X h e).initial.arithmetic.Fmod)
          (((nativeOriginalInputDonors_of_contract X h e).initial_arithmetic ▸
            nativePlaceIndexEquiv X) v)) :
    NativeOldBindingDonorsExist X :=
  nativeOldBindingDonorsExist_of_p6BridgeDonors X
    (p6BridgeDonors_of_contract X h e R F)

end LeanFormal.IUT.N8Closure.C1Actual
end