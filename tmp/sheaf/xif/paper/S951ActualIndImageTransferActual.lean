import tmp.sheaf.xif.paper.S940Ind3ImageActual
import tmp.sheaf.xif.paper.S928ActualIndImageGapActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S951ActualIndImageTransferActual

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
open LeanFormal.IUT.XiFPaper.S928ActualIndImageGapActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe ua uv upi ui uVQ
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Ind1 actual source carrier: reindexed tensor packet. -/
abbrev S951Ind1Carrier (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) : Type :=
  (⨂[Real] i : Capsule j.val,
    DirectSumFactor (C.logShell j) vQ (P.perm.symm i))

/-- Ind2 actual source carrier: tensor packet. -/
abbrev S951Ind2Carrier (j : Fin (capsuleLevels l)) (vQ : C.VQ) : Type :=
  SourceProcessionCapsuleContract.tensorPacket Real C j vQ

/-- Ind3 actual source carrier: TimesMuQuotient stage. -/
abbrev S951Ind3Carrier (v : V) (m : Int) : Type :=
  ActualInd3Stage (I := I) v m

/-- Exact minimal type-corrected transfer: actual S940 image sources, maps to
qVFamTensorBlock, and actuality Props.  No map is fabricated. -/
structure ActualIndImageTransfer
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v) : Type where
  toBlock1 : S951Ind1Carrier (A := A) (C := C) j vQ P → qVFamTensorBlock T b
  toBlock2 : S951Ind2Carrier (C := C) j vQ → qVFamTensorBlock T b
  toBlock3 : S951Ind3Carrier (I := I) v m → qVFamTensorBlock T b
  base1 : Set (ActualTensorPacket C j vQ)
  base2 : Set (S951Ind2Carrier (C := C) j vQ)
  base3 : Set (S951Ind3Carrier (I := I) v m)
  image1 : Set (qVFamTensorBlock T b)
  image2 : Set (qVFamTensorBlock T b)
  image3 : Set (qVFamTensorBlock T b)
  image1_eq : image1 = toBlock1 '' ind1ImageOfSet A C j vQ P base1
  image2_eq : image2 = toBlock2 '' ind2ImageOfSet C j vQ f base2
  image3_eq : image3 = toBlock3 '' ind3ImageOfSet (I := I) v m g base3
  ind1_actual : Prop
  ind2_actual : Prop
  ind3_actual : Prop

/-- Exact transfer obligation.  No inhabitant is asserted. -/
def ActualIndImageTransferRequired : Prop :=
  ∃ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v),
    Nonempty (ActualIndImageTransfer (l := l) (V := V) (I := I) (A := A) (C := C)
      (T := T) (b := b) j vQ P f v m g)


/-- A type-corrected transfer yields S928's exact ActualIndImageData: the new
source carriers are the actual qVFam image sets. -/
noncomputable def actualIndImageDataOfTransfer
    {j : Fin (capsuleLevels l)} {vQ : C.VQ}
    {P : PrcAutomorphism A j} {f : Capsule j.val → Realˣ}
    {v : V} {m : Int}
    {g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v}
    (X : ActualIndImageTransfer (l := l) (V := V) (I := I) (A := A) (C := C)
      (T := T) (b := b) j vQ P f v m g) :
    ActualIndImageData (l := l) T b where
  Ind1 := X.image1
  Ind2 := X.image2
  Ind3 := X.image3
  toBlock1 y := y.1
  toBlock2 y := y.1
  toBlock3 y := y.1
  image1 := X.image1
  image2 := X.image2
  image3 := X.image3
  image1_eq_range := by
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact hz
  image2_eq_range := by
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact hz
  image3_eq_range := by
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact hz
  ind1_actual := X.ind1_actual
  ind2_actual := X.ind2_actual
  ind3_actual := X.ind3_actual

theorem actualIndImageDataOfTransfer_nonempty
    (h : ActualIndImageTransferRequired (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) b) :
    Nonempty (ActualIndImageData (l := l) T b) := by
  rcases h with ⟨j, vQ, P, f, v, m, g, ⟨X⟩⟩
  exact ⟨actualIndImageDataOfTransfer (l := l) (V := V) (I := I) (A := A) (C := C)
    (T := T) (b := b) X⟩

end LeanFormal.IUT.XiFPaper.S951ActualIndImageTransferActual

end
