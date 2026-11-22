import tmp.sheaf.xif.paper.S951ActualIndImageTransferActual
import tmp.sheaf.xif.paper.S940Ind3ImageActual

/-! # S963: actual toBlock transfer from qVFam projection data

S940 supplies the actual Ind1/Ind2/Ind3 source carriers and their actual images.
A qVFamTensorBlock projection from each source carrier is the only missing map.
Given the three projections, the S951 ActualIndImageTransfer is constructed
with images equal to the actual projection ranges; no default/zero map is used.
The exact minimal input is S963IndProjectionTripleRequired. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S963ActualToBlockProjectionActual

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

universe ua uv upi ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing qVFam projections from the three actual Ind carriers. -/
structure S963IndProjectionTriple
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v) where
  toBlock1 : S951Ind1Carrier (A := A) (C := C) j vQ P → qVFamTensorBlock T b
  toBlock2 : S951Ind2Carrier (C := C) j vQ → qVFamTensorBlock T b
  toBlock3 : S951Ind3Carrier (I := I) v m → qVFamTensorBlock T b

/-- Given actual projections, construct the S951 actual transfer.  The images
are the actual projection ranges, so they are not empty/default objects. -/
noncomputable def s963TransferOfProjections
    {j : Fin (capsuleLevels l)} {vQ : C.VQ}
    {P : PrcAutomorphism A j} {f : Capsule j.val → Realˣ}
    {v : V} {m : Int}
    {g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v}
    (proj : S963IndProjectionTriple (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) j vQ P f v m g) :
    ActualIndImageTransfer (l := l) (V := V) (I := I) (A := A) (C := C)
      (T := T) (b := b) j vQ P f v m g where
  toBlock1 := proj.toBlock1
  toBlock2 := proj.toBlock2
  toBlock3 := proj.toBlock3
  base1 := Set.univ
  base2 := Set.univ
  base3 := Set.univ
  image1 := proj.toBlock1 '' ind1ImageOfSet A C j vQ P (Set.univ)
  image2 := proj.toBlock2 '' ind2ImageOfSet C j vQ f (Set.univ)
  image3 := proj.toBlock3 '' ind3ImageOfSet (I := I) v m g (Set.univ)
  image1_eq := rfl
  image2_eq := rfl
  image3_eq := rfl
  ind1_actual := (Set.range proj.toBlock1).Nonempty
  ind2_actual := (Set.range proj.toBlock2).Nonempty
  ind3_actual := (Set.range proj.toBlock3).Nonempty

/-- Existence of actual projections yields S951's transfer obligation. -/
theorem s963ActualIndImageTransferRequired_of_projections
    (h : ∃ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
      (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
      (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v),
      Nonempty (S963IndProjectionTriple (l := l) (V := V) (I := I)
        (A := A) (C := C) (T := T) (b := b) j vQ P f v m g)) :
    ActualIndImageTransferRequired (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) b := by
  rcases h with ⟨j, vQ, P, f, v, m, g, ⟨proj⟩⟩
  exact ⟨j, vQ, P, f, v, m, g,
    ⟨s963TransferOfProjections (l := l) (V := V) (I := I) (A := A) (C := C)
      (T := T) (b := b) proj⟩⟩

/-- Exact minimal required qVFam projection data. -/
def S963IndProjectionTripleRequired : Prop :=
  ∃ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v),
    Nonempty (S963IndProjectionTriple (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) j vQ P f v m g)

end LeanFormal.IUT.XiFPaper.S963ActualToBlockProjectionActual

end
