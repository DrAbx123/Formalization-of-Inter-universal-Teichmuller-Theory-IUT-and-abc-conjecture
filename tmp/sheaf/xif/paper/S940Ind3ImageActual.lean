import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual
import tmp.sheaf.xif.paper.Ind1AutomorphismTensorActionActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual
import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # S940: actual Ind1/Ind2/Ind3 images

Ind1 image is the PrcAutomorphismTensorAction image in the reindexed tensor
packet.  Ind2 image is the ind2TensorEquiv image on the tensor packet.
Ind3 image is the actual times-mu stage action image on TimesMuQuotient.
All three image sets are nonempty as soon as the base set is nonempty.
A qVFamTensorBlock Ind image still needs an explicit packet transport; that is
the exact minimal gap.  No empty/theta-only object is used. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S940Ind3ImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe ua uv upi umon ui uR uVQ

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)

/-- Ind1 image in the reindexed tensor packet. -/
noncomputable def ind1ImageOfSet
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j)
    (base : Set (ActualTensorPacket C j vQ)) :
    Set ((⨂[Real] i : Capsule j.val,
      DirectSumFactor (C.logShell j) vQ (P.perm.symm i))) :=
  (PrcAutomorphismTensorAction A C j vQ P) '' base

theorem ind1ImageOfSet_nonempty
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j)
    {base : Set (ActualTensorPacket C j vQ)} (hbase : base.Nonempty) :
    (ind1ImageOfSet A C j vQ P base).Nonempty :=
  hbase.image _

/-- Ind2 image on the tensor packet. -/
noncomputable def ind2ImageOfSet
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : Capsule j.val → Realˣ)
    (base : Set (SourceProcessionCapsuleContract.tensorPacket Real C j vQ)) :
    Set (SourceProcessionCapsuleContract.tensorPacket Real C j vQ) :=
  (ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f) '' base

theorem ind2ImageOfSet_nonempty
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : Capsule j.val → Realˣ)
    {base : Set (SourceProcessionCapsuleContract.tensorPacket Real C j vQ)}
    (hbase : base.Nonempty) :
    (ind2ImageOfSet C j vQ f base).Nonempty :=
  hbase.image _

/-- Ind3 image at a column and place, under the actual times-mu stage action. -/
noncomputable def ind3ImageOfSet
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    (base : Set (ActualInd3Stage (I := I) v m)) :
    Set (ActualInd3Stage (I := I) v m) :=
  (actualInd3StageAction (I := I) v m g : MulAut (ActualInd3Stage (I := I) v m)) '' base

theorem ind3ImageOfSet_nonempty
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    {base : Set (ActualInd3Stage (I := I) v m)} (hbase : base.Nonempty) :
    (ind3ImageOfSet (I := I) (v := v) (m := m) g base).Nonempty :=
  hbase.image _

/-- Exact transport needed for a qVFamTensorBlock Ind image. -/
structure S940PacketToQVFamTransport
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  toQVFam : ActualTensorPacket C j vQ → qVFamTensorBlock T b
  base : Set (ActualTensorPacket C j vQ)
  base_nonempty : base.Nonempty

/-- Actual nonempty image through any supplied transport. -/
theorem packetImageQVFam_nonempty
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (D : S940PacketToQVFamTransport (l := l)
      (C := C) (j := j) (vQ := vQ) T b) :
    (D.toQVFam '' D.base).Nonempty :=
  D.base_nonempty.image _

/-- Exact minimal datum for an actual qVFamTensorBlock Ind image. -/
def S940QVFamIndImageRequired : Prop :=
  ∃ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)),
    Nonempty (S940PacketToQVFamTransport (l := l)
      (C := C) (j := j) (vQ := vQ) T b)

end LeanFormal.IUT.XiFPaper.S940Ind3ImageActual

end
