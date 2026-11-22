import tmp.sheaf.xif.paper.S940Ind3ImageActual
import tmp.sheaf.xif.paper.S951ActualIndImageTransferActual
import tmp.sheaf.xif.paper.MultiradialProcessionActual

/-! # S1142: Ind1/2/3 on the actual paper carrier

S939 identifies the paper S carrier as the procession tensor packet
`ActualTensorPacket C j vQ`, while the qVFamTensorBlock is only the model
carrier.  This file puts the Ind images directly on the paper carrier: Ind1 and
Ind2 are actual (Ind1 is the source action followed by the inverse reindexing);
Ind3 still needs an explicit transport to the paper carrier, recorded as an
exact structure.  No scalar surrogate is used. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1142IndPaperCarrierActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.S940Ind3ImageActual
open LeanFormal.IUT.XiFPaper.S951ActualIndImageTransferActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}

/-- Actual paper S carrier: the procession tensor packet, not qVFamTensorBlock. -/
abbrev PaperFinalCarrier (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) : Type :=
  ActualTensorPacket C j vQ

/-- Actual Ind1 image on the paper carrier: source Ind1 image composed with
the inverse reindexing `(PrcAutomorphismTensorAction P).symm`. -/
noncomputable def paperInd1Image
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (base : Set (ActualTensorPacket C j vQ)) :
    Set (PaperFinalCarrier A C j vQ) :=
  (PrcAutomorphismTensorAction A C j vQ P).symm ''
    (ind1ImageOfSet A C j vQ P base)

theorem paperInd1Image_nonempty
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) {base : Set (ActualTensorPacket C j vQ)}
    (hbase : base.Nonempty) :
    (paperInd1Image A C j vQ P base).Nonempty :=
  hbase.image _

/-- Actual Ind2 image on the paper carrier. -/
noncomputable def paperInd2Image
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : Capsule j.val → Realˣ)
    (base : Set (PaperFinalCarrier A C j vQ)) :
    Set (PaperFinalCarrier A C j vQ) :=
  (ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f) '' base

theorem paperInd2Image_nonempty
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : Capsule j.val → Realˣ)
    {base : Set (PaperFinalCarrier A C j vQ)} (hbase : base.Nonempty) :
    (paperInd2Image A C j vQ f base).Nonempty :=
  hbase.image _

/-- Exact minimal Ind3 transport to the actual paper carrier.  The Ind3 action
lives on TimesMuQuotient; no map to the tensor packet is supplied by the tree. -/
structure PaperInd3Transport
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v) where
  toPaper : ActualInd3Stage (I := I) v m → PaperFinalCarrier A C j vQ
  base : Set (ActualInd3Stage (I := I) v m)
  base_nonempty : base.Nonempty
  image : Set (PaperFinalCarrier A C j vQ)
  image_eq : image = toPaper '' ind3ImageOfSet (I := I) v m g base

def PaperInd3TransportRequired
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v) : Prop :=
  Nonempty (PaperInd3Transport A C j vQ v m g)

/-- Exact Ind3 image on the paper carrier, conditional on the transport. -/
noncomputable def paperInd3Image
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    (X : PaperInd3Transport A C j vQ v m g) :
    Set (PaperFinalCarrier A C j vQ) :=
  X.image

theorem paperInd3Image_nonempty
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    (X : PaperInd3Transport A C j vQ v m g) :
    (paperInd3Image A C j vQ v m g X).Nonempty :=
  X.base_nonempty.image X.toPaper

/-- Actual Ind1/Ind2 images plus the exact Ind3 transfer on the paper carrier. -/
structure PaperIndImageDataFinal
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) where
  P : PrcAutomorphism A j
  f : Capsule j.val → Realˣ
  base1 : Set (ActualTensorPacket C j vQ)
  base1_nonempty : base1.Nonempty
  base2 : Set (PaperFinalCarrier A C j vQ)
  base2_nonempty : base2.Nonempty
  ind1Image : Set (PaperFinalCarrier A C j vQ)
  ind1Image_eq : ind1Image = paperInd1Image A C j vQ P base1
  ind2Image : Set (PaperFinalCarrier A C j vQ)
  ind2Image_eq : ind2Image = paperInd2Image A C j vQ f base2
  ind3Transfer : Prop
  ind3Image : Set (PaperFinalCarrier A C j vQ)

/-- Constructor: Ind1/Ind2 images actual; Ind3 image/transfer passed exactly. -/
noncomputable def paperIndImageDataFinal
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (base1 : Set (ActualTensorPacket C j vQ)) (h1 : base1.Nonempty)
    (base2 : Set (PaperFinalCarrier A C j vQ)) (h2 : base2.Nonempty)
    (ind3Transfer : Prop)
    (ind3Image : Set (PaperFinalCarrier A C j vQ)) :
    PaperIndImageDataFinal A C j vQ where
  P := P
  f := f
  base1 := base1
  base1_nonempty := h1
  base2 := base2
  base2_nonempty := h2
  ind1Image := paperInd1Image A C j vQ P base1
  ind1Image_eq := rfl
  ind2Image := paperInd2Image A C j vQ f base2
  ind2Image_eq := rfl
  ind3Transfer := ind3Transfer
  ind3Image := ind3Image

theorem paperIndImageDataFinal_ind1_nonempty
    (D : PaperIndImageDataFinal A C j vQ) :
    D.ind1Image.Nonempty :=
  D.base1_nonempty.image _

theorem paperIndImageDataFinal_ind2_nonempty
    (D : PaperIndImageDataFinal A C j vQ) :
    D.ind2Image.Nonempty :=
  D.base2_nonempty.image _

end LeanFormal.IUT.XiFPaper.S1142IndPaperCarrierActualAdapted
end
