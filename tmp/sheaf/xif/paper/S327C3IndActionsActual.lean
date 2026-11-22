import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.Ind1AutomorphismTensorActionActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual
import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual

-- S327: conditional actual Ind1/2/3 action data on C3LogShellTensorBlock,
-- using existing actual actions on ActualTensorPacket / ActualInd3Stage.
-- Explicit carrier identifications are inputs; no fake identity is used.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S327C3IndActionsActual

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

universe uv

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{0, uv, 0, 0, 0} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V)

structure C3IndTransport where
  toPacket : C3LogShellTensorBlock (I := I) C3 ≃ ActualTensorPacket C j vQ
  fromReindexed : ∀ P : PrcAutomorphism A j,
    (⨂[Real] i : Capsule j.val, DirectSumFactor (C.logShell j) vQ (P.perm.symm i))
      ≃ C3LogShellTensorBlock (I := I) C3
  toStage : C3LogShellTensorBlock (I := I) C3 ≃ ActualInd3Stage (I := I) v 0

noncomputable def ind1Action (S : C3IndTransport (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v))
    (P : PrcAutomorphism A j) :
    C3LogShellTensorBlock (I := I) C3 ≃ C3LogShellTensorBlock (I := I) C3 :=
  S.toPacket.trans ((PrcAutomorphismTensorAction A C j vQ P).toEquiv.trans (S.fromReindexed P))

noncomputable def ind2Action (S : C3IndTransport (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v))
    (f : Capsule j.val → Realˣ) :
    C3LogShellTensorBlock (I := I) C3 ≃ C3LogShellTensorBlock (I := I) C3 :=
  S.toPacket.trans ((ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f).toEquiv.trans S.toPacket.symm)

noncomputable def ind3Action (S : C3IndTransport (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v))
    (g : (I.fPrimeStripAt 1 0).toDPrimeStrip.Pi v) :
    C3LogShellTensorBlock (I := I) C3 ≃ C3LogShellTensorBlock (I := I) C3 :=
  S.toStage.trans ((actualInd3StageAction (I := I) v 0 g).toEquiv.trans S.toStage.symm)

structure C3IndImageSetup extends C3IndTransport (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v) where
  baseImage : Set (C3LogShellTensorBlock (I := I) C3)

noncomputable def C3IndImageUnion
    (S : C3IndImageSetup (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v)) :
    Set (C3LogShellTensorBlock (I := I) C3) :=
  S.baseImage ∪
    (Set.iUnion (fun P : PrcAutomorphism A j =>
      (ind1Action (S := S.toC3IndTransport) (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v) P) '' S.baseImage)) ∪
    (Set.iUnion (fun f : Capsule j.val → Realˣ =>
      (ind2Action (S := S.toC3IndTransport) (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v) f) '' S.baseImage)) ∪
    (Set.iUnion (fun g : (I.fPrimeStripAt 1 0).toDPrimeStrip.Pi v =>
      (ind3Action (S := S.toC3IndTransport) (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v) g) '' S.baseImage))

structure C3IndActionCarrierGap where
  transport : C3IndTransport (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v)
  baseImage : Set (C3LogShellTensorBlock (I := I) C3)

def C3IndActionCarrierGapRequired : Prop :=
  Nonempty (C3IndActionCarrierGap (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v))

#check C3IndTransport
#check ind1Action
#check ind2Action
#check ind3Action
#check C3IndImageUnion
#check C3IndActionCarrierGap

end LeanFormal.IUT.XiFPaper.S327C3IndActionsActual

end