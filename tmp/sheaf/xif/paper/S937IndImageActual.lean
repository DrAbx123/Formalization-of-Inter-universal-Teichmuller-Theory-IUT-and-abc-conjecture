import tmp.sheaf.xif.paper.S940Ind3ImageActual

/-! # S937: corrected Ind1/Ind2/Ind3 actual image layer

Thin corrected layer over S940.  Ind1 image lives in the reindexed tensor
packet (not an endomorphism); Ind2 image is on the tensor packet; Ind3 image
is the TimesMuQuotient stage-action image.  A qVFamTensorBlock image needs an
explicit transport (exact, from S940). -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S937IndImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open LeanFormal.IUT.XiFPaper.S940Ind3ImageActual

universe ua uv upi ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)

theorem s937Ind1Image_nonempty
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) (P : PrcAutomorphism A j)
    {base : Set (ActualTensorPacket C j vQ)} (hbase : base.Nonempty) :
    (ind1ImageOfSet A C j vQ P base).Nonempty :=
  ind1ImageOfSet_nonempty A C j vQ P hbase

theorem s937Ind2Image_nonempty
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) (f : Capsule j.val → Realˣ)
    {base : Set (SourceProcessionCapsuleContract.tensorPacket Real C j vQ)}
    (hbase : base.Nonempty) :
    (ind2ImageOfSet C j vQ f base).Nonempty :=
  ind2ImageOfSet_nonempty C j vQ f hbase

theorem s937Ind3Image_nonempty
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    {base : Set (ActualInd3Stage (I := I) v m)} (hbase : base.Nonempty) :
    (ind3ImageOfSet (I := I) (v := v) (m := m) g base).Nonempty :=
  ind3ImageOfSet_nonempty (I := I) (v := v) (m := m) g hbase

def S937QVFamIndImageRequired : Prop :=
  S940QVFamIndImageRequired (l := l) (V := V) (I := I) (C := C)

end LeanFormal.IUT.XiFPaper.S937IndImageActual

end