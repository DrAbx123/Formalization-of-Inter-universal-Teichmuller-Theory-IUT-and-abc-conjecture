import tmp.sheaf.n8.closure.C1FromOldBindingDonors
import tmp.sheaf.n8.closure.P6Bridge

/-! # C1 data from the P6 donor package

P6BridgeDonors is an actual structure with NativeOriginalInputDonors and NativePlaceBindingDonors fields; it therefore yields NativeOldBindingDonorsExist and then C1ActualData/SourceInputBinding.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.C1BridgeProof
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.P6Bridge

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem nativeOldBindingDonorsExist_of_p6BridgeDonors
    (D : P6BridgeDonors X) : NativeOldBindingDonorsExist X :=
  ⟨D.inputDonors, ⟨D.bindingDonors⟩⟩

theorem nativeOldBindingDonorsExist_of_p6BridgeDonorsExist
    (h : P6BridgeDonorsExist X) : NativeOldBindingDonorsExist X :=
  nativeOldBindingDonorsExist_of_p6BridgeDonors X (Classical.choice h)

theorem c1ActualData_exists_of_p6BridgeDonors
    (D : P6BridgeDonors X) :
    ∃ D' : NativeOriginalInputDonors X,
      Nonempty (C1ActualData (nativeOriginalInputOfDonors X D')) :=
  c1ActualData_exists_of_nativeOldBindingDonors X
    (nativeOldBindingDonorsExist_of_p6BridgeDonors X D)

theorem sourceInputBinding_exists_of_p6BridgeDonorsExist
    (h : P6BridgeDonorsExist X) :
    ∃ D : NativeOriginalInputDonors X,
      Nonempty (SourceInputBinding (nativeOriginalInputOfDonors X D)) :=
  sourceInputBinding_exists_of_nativeOldBindingDonors X
    (nativeOldBindingDonorsExist_of_p6BridgeDonorsExist X h)

theorem p6BridgeDonorsExist_iff_nativeOldBindingDonorsExist :
    P6BridgeDonorsExist X ↔ NativeOldBindingDonorsExist X := by
  constructor
  · exact nativeOldBindingDonorsExist_of_p6BridgeDonorsExist X
  · rintro ⟨D, P⟩
    exact ⟨D, Classical.choice P⟩

end LeanFormal.IUT.N8Closure.C1Actual
end