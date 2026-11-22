import tmp.sheaf.xif.paper.S951ActualIndImageTransferActual
import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual
import tmp.sheaf.xif.paper.PaperFinalLValuedTensorCarrierActual

/-! # S966: toBlock maps from S940 Ind carriers

The S940 carriers are tensor packets over Real (Ind1/Ind2) or TimesMuQuotient
stages (Ind3).  The qVFam/FinalL carriers are p-adic (Qp/FinalL).  The tree has
the actual embedding qVFamToLValued : qVFamBlock -> FinalLValuedCarrier, but no
canonical map from the Real tensor packets to either target.  This file records
the exact maps/injectivity/type conditions; no map is fabricated. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S966ActualToBlockActual
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
open LeanFormal.IUT.XiFPaper.S940Ind3ImageActual
open LeanFormal.IUT.XiFPaper.S951ActualIndImageTransferActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open MeasureTheory

universe ua uv upi ui uVQ
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact qVFam toBlock data from the S940 carriers. -/
structure S966ToQVFamActual
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v) where
  toBlock1 : S951Ind1Carrier (A := A) (C := C) j vQ P → qVFamTensorBlock T b
  toBlock2 : S951Ind2Carrier (C := C) j vQ → qVFamTensorBlock T b
  toBlock3 : S951Ind3Carrier (I := I) v m → qVFamTensorBlock T b
  injective1 : Prop
  injective2 : Prop
  injective3 : Prop
  image_compat1 : Prop
  image_compat2 : Prop
  image_compat3 : Prop

/-- Exact qVFam toBlock obligation. -/
def S966ToQVFamRequired : Prop :=
  ∃ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v),
    Nonempty (S966ToQVFamActual (l := l) (V := V) (I := I) (A := A) (C := C)
      (T := T) (b := b) j vQ P f v m g)

/-- Target FinalL-valued maps, with the actual qVFamToLValued available as the
qVFam-block -> FinalL embedding. -/
structure S966ToFinalLActual
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v) where
  toFinalL1 : S951Ind1Carrier (A := A) (C := C) j vQ P →
    FinalLValuedCarrier T b
  toFinalL2 : S951Ind2Carrier (C := C) j vQ → FinalLValuedCarrier T b
  toFinalL3 : S951Ind3Carrier (I := I) v m → FinalLValuedCarrier T b
  injective1 : Prop
  injective2 : Prop
  injective3 : Prop
  factors_through_qVFam1 : Prop
  factors_through_qVFam2 : Prop
  factors_through_qVFam3 : Prop

/-- If a qVFam toBlock exists, composing with the actual tensor embedding
qVFamToLValued gives the FinalL-valued maps. -/
noncomputable def toFinalL_of_toQVFam
    {j : Fin (capsuleLevels l)} {vQ : C.VQ}
    {P : PrcAutomorphism A j} {f : Capsule j.val → Realˣ}
    {v : V} {m : Int}
    {g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v}
    (X : S966ToQVFamActual (l := l) (V := V) (I := I) (A := A) (C := C)
      (T := T) (b := b) j vQ P f v m g) :
    S966ToFinalLActual (l := l) (V := V) (I := I) (A := A) (C := C)
      (T := T) (b := b) j vQ P f v m g where
  toFinalL1 := qVFamToLValued (l := l) T b ∘ X.toBlock1
  toFinalL2 := qVFamToLValued (l := l) T b ∘ X.toBlock2
  toFinalL3 := qVFamToLValued (l := l) T b ∘ X.toBlock3
  injective1 := X.injective1
  injective2 := X.injective2
  injective3 := X.injective3
  factors_through_qVFam1 := True
  factors_through_qVFam2 := True
  factors_through_qVFam3 := True

end LeanFormal.IUT.XiFPaper.S966ActualToBlockActual
end