import tmp.sheaf.n8.closure.C1ActualDataNative
import tmp.sheaf.n8.closure.C1BridgeProof

/-! # C1 actual data from the old binding donors

The exact native donor proposition NativeOldBindingDonorsExist supplies a NativeOriginalInputDonors package and a NativePlaceBindingDonors package; these construct C1ActualData and SourceInputBinding.
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
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem c1ActualData_exists_of_nativeOldBindingDonors
    (h : NativeOldBindingDonorsExist X) :
    ∃ D : NativeOriginalInputDonors X,
      Nonempty (C1ActualData (nativeOriginalInputOfDonors X D)) := by
  rcases h with ⟨D, P⟩
  exact ⟨D, ⟨c1ActualDataOfNativeDonors X D (Classical.choice P)⟩⟩

theorem sourceInputBinding_exists_of_nativeOldBindingDonors
    (h : NativeOldBindingDonorsExist X) :
    ∃ D : NativeOriginalInputDonors X,
      Nonempty (SourceInputBinding (nativeOriginalInputOfDonors X D)) := by
  rcases h with ⟨D, P⟩
  exact ⟨D, ⟨sourceInputBindingOfNativeDonors X D (Classical.choice P)⟩⟩

end LeanFormal.IUT.N8Closure.C1Actual
end