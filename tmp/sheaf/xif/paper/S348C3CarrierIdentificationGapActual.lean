import tmp.sheaf.xif.paper.S327C3IndActionsActual

-- S348: exact carrier-identification gap.  The C3 arithmetic block and the
-- procession capsule packet have different arbitrary indices/factor types;
-- no source identification exists.  Given explicit transport, S327 actions
-- become actual; without it, no identity/fake equivalence is asserted.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S348C3CarrierIdentificationGapActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open LeanFormal.IUT.XiFPaper.S327C3IndActionsActual

universe uv

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{0, uv, 0, 0, 0} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V)

structure C3CarrierIdentification where
  indexEquiv : C3.tensorIndex ≃ Capsule j.val
  toPacket : C3LogShellTensorBlock (I := I) C3 ≃ ActualTensorPacket C j vQ
  fromReindexed : ∀ P : PrcAutomorphism A j,
    (⨂[Real] i : Capsule j.val, DirectSumFactor (C.logShell j) vQ (P.perm.symm i))
      ≃ C3LogShellTensorBlock (I := I) C3
  toStage : C3LogShellTensorBlock (I := I) C3 ≃ ActualInd3Stage (I := I) v 0

noncomputable def c3IndTransportOfIdentification
    (D : C3CarrierIdentification (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v)) :
    C3IndTransport (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v) where
  toPacket := D.toPacket
  fromReindexed := D.fromReindexed
  toStage := D.toStage

def C3CarrierIdentificationGapRequired : Prop :=
  Nonempty (C3CarrierIdentification (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v))

#check C3CarrierIdentification
#check c3IndTransportOfIdentification
#check C3CarrierIdentificationGapRequired

end LeanFormal.IUT.XiFPaper.S348C3CarrierIdentificationGapActual

end