import tmp.sheaf.xif.paper.C3IQSpecialCaseActual
import tmp.sheaf.xif.paper.S327C3IndActionsActual

/-!
# S372: A-packet / C3-block special-case transport exact gap

`S327C3IndActionsActual.C3IndTransport.toPacket` is exactly the missing carrier
transport from `C3LogShellTensorBlock` to the actual A tensor packet.  The S362
special-case equivalence only coords the C3 block; it does not identify the A
packet carrier, whose source contract is over `R` (the actual A packet is built
from `C.place` and `C.logShell j` and is not canonically the same carrier as the
completion tensor block).  Therefore the special-case transport remains the
explicit input recorded below; no identity is fabricated.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S372APacketC3TransportGapActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S327C3IndActionsActual
open LeanFormal.IUT.XiFPaper.C3IQSpecialCaseActual

universe uv

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V)

/-- Special-case A-packet/C3 transport data aligned with S362: the C3 tensor
index is the capsule index, and the transport is the explicit actual carrier
identification required by S327. -/
structure APacketC3SpecialCaseTransport where
  c3Index_eq_capsule : C3.tensorIndex = Capsule j.val
  transport : C3IndTransport (A := A) (C := C) (C3 := C3)
    (j := j) (vQ := vQ) (v := v)
  region_maps : Prop
  iq_span_maps : Prop

/-- Exact-missing predicate for the A-packet/C3 special-case transport. -/
def APacketC3SpecialCaseTransportRequired : Prop :=
  Nonempty (APacketC3SpecialCaseTransport (A := A) (C := C) (C3 := C3)
    (j := j) (vQ := vQ) (v := v))

/-- S362's C3 coordinate equivalence is a prerequisite, not an A-packet
identification; this name records that the two objects are distinct. -/
def C3CoordinateEquivIsNotAPacketTransport : Prop :=
  APacketC3SpecialCaseTransportRequired (A := A) (C := C) (C3 := C3)
    (j := j) (vQ := vQ) (v := v)

end LeanFormal.IUT.XiFPaper.S372APacketC3TransportGapActual
end
