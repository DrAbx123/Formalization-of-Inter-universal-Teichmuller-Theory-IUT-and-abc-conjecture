import tmp.sheaf.xif.paper.PaperAPureCarrierActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

/-! # Conditional A-to-C3 index transport

Given an explicit equivalence e : Capsule j ≃ C3.tensorIndex, the pure A tensor
packet over ℤ reindexes to the tensor over C3.tensorIndex with the same ℤ
factors.  This is an actual PiTensorProduct.reindex equivalence.

Transport to the full C3LogShellTensorBlock additionally requires factor maps
ℤ → C3LogShellFiber and a tuple-index comparison; those are recorded as exact
missing data, not fabricated. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.PaperAC3IndexTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperAPureCarrierActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

universe ua uv upi umon ui

variable {l : PrimeGeFive}

/-- Actual index reindexing from the pure A packet to the tensor over
C3.tensorIndex with the same ℤ factors, given e. -/
noncomputable def paperAIndexTransport
    {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (V := V) I) {j : Nat}
    (e : Capsule j ≃ C3.tensorIndex) :
    PaperATensorPacket j ≃ₗ[ℤ]
      (⨂[ℤ] _i : C3.tensorIndex, (Unit → ℤ)) := by
  exact PiTensorProduct.reindex ℤ (fun _ : Capsule j => (Unit → ℤ)) e


/-- Exact missing data for a tensor map into the full C3LogShellTensorBlock:
reindex e plus factor linear maps into the C3 log-shell fibers and tuple
compatibility.  Not asserted to exist. -/
structure PaperAToC3TensorBlockTransportData
    {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (V := V) I) (j : Nat) where
  indexEquiv : Capsule j ≃ C3.tensorIndex
  factorMap : Prop
  tupleCompat : Prop

def PaperAToC3TensorBlockTransportRequired
    {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (V := V) I) (j : Nat) : Prop :=
  Nonempty (PaperAToC3TensorBlockTransportData (l := l) C3 j)

end LeanFormal.IUT.XiFPaper.PaperAC3IndexTransportActual

end
