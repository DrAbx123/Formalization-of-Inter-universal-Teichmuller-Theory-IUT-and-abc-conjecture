import tmp.sheaf.n8.closure.C1FromP6Donors

/-! # Canonical C1 donor package

One canonical interface for the C1 donor gap: P6BridgeDonors (equivalently NativeOldBindingDonorsExist). The older C1ActualDataComponents is a weak contract-over-arithmetic wrapper; this file is the canonical source-facing package.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C1BridgeProof
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Canonical C1 donor package: native input donors plus old place/R/fiber binding. -/
abbrev C1DonorPackage (X : N8NativeInput l) := P6BridgeDonors X

abbrev C1DonorPackageExists (X : N8NativeInput l) : Prop := P6BridgeDonorsExist X

theorem c1DonorPackageExists_iff_nativeOldBindingDonorsExist :
    C1DonorPackageExists X ↔ NativeOldBindingDonorsExist X :=
  p6BridgeDonorsExist_iff_nativeOldBindingDonorsExist X

theorem c1ActualData_exists_of_canonicalDonors (D : C1DonorPackage X) :
    ∃ D' : NativeOriginalInputDonors X,
      Nonempty (C1ActualData (nativeOriginalInputOfDonors X D')) :=
  c1ActualData_exists_of_p6BridgeDonors X D

theorem sourceInputBinding_exists_of_canonicalDonorsExist
    (h : C1DonorPackageExists X) :
    ∃ D : NativeOriginalInputDonors X,
      Nonempty (SourceInputBinding (nativeOriginalInputOfDonors X D)) :=
  sourceInputBinding_exists_of_p6BridgeDonorsExist X h

/-- Canonical donor package to the actual old C1 bridge consumed by C6PaperInput. -/
noncomputable def nativeOldC1BridgeOfCanonicalDonors (D : C1DonorPackage X) :
    NativeOldC1Bridge X :=
  D.toNativeOldC1Bridge

theorem nativeOldC1BridgeExists_of_canonicalDonors (D : C1DonorPackage X) :
    NativeOldC1BridgeExists X :=
  ⟨nativeOldC1BridgeOfCanonicalDonors X D⟩

theorem nativeBridgeComponent_of_canonicalDonors (h : C1DonorPackageExists X) :
    Nonempty (NativeOldC1Bridge X) :=
  ⟨nativeOldC1BridgeOfCanonicalDonors X (Classical.choice h)⟩

end LeanFormal.IUT.N8Closure.C1Actual
end