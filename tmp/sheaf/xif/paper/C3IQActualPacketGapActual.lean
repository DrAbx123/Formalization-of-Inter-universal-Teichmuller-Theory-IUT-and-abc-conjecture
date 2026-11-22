import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket

/-!
# Actual IQ tensor carrier and C3 <-> IQ linear-equivalence gap

The C3 packet already has an actual tensor-product carrier:
`ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple`, with actual local
log-shell tensor integral region and its actual Q-span.  The source
`SourceLogShellIQTensorPacket` model is a reduced function-space/multiplication
model; it is not an actual tensor product of ind-topological modules.

This file records the actual C3 carrier and the exact missing linear
equivalence from that carrier to the source IQ packet.  No span equality is
asserted in place of the missing equivalence.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.C3IQActualPacketGapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual tensor-product carrier of the IQ packet: the C3 arithmetic
tensor block over the C3 tensor index/tuple. -/
abbrev ActualIQTensorCarrier : Type :=
  C3LogShellTensorBlock C3

/-- The actual C3 tensor IQ packet (actual region, compactness, actual Haar
and actual Q-span). -/
abbrev ActualIQTensorPacket : Type :=
  ActualC3LogShellTensorPacket (C3 := C3)

variable (D : C3.tensorIndex → SourceLogShellDatum)

/-- Exact missing actual ℚ-linear equivalence between the actual tensor-product
IQ carrier and the source reduced IQ function-space packet.  The C3 side is a
genuine tensor product; the source side is the reduced model. -/
structure C3IQActualLinearEquivalence where
  equiv : ActualIQTensorCarrier C3 ≃ₗ[ℚ]
    ((i : C3.tensorIndex) → (D i).K)
  region_maps : Prop
  iq_span_maps : Prop
  haar_compatibility : Prop

/-- Exact-missing predicate for the actual C3/IQ linear equivalence. -/
def C3IQActualLinearEquivalenceRequired : Prop :=
  Nonempty (C3IQActualLinearEquivalence C3 D)

/-- The reduced source IQ tensor packet remains a separate reduced model; it is
not identified with the actual tensor-product carrier by this file. -/
def ReducedIQPacketNotActualTensorCarrier : Prop :=
  C3IQActualLinearEquivalenceRequired C3 D

end LeanFormal.IUT.XiFPaper.C3IQActualPacketGapActual
end
