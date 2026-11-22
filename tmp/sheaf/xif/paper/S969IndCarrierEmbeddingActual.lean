import tmp.sheaf.xif.paper.S963ActualToBlockProjectionActual
import tmp.sheaf.xif.paper.PaperFinalLValuedTensorCarrierActual

/-! # S969: exact minimal embedding data for the S963 projection triple

S940 gives the actual Ind carriers.  The qVFam block is a Qp-vector space,
while the Ind carriers are Real-vector spaces, so there is no canonical
Qp-linear projection.  The exact minimal datum is an additive injection
(embedding) from each actual carrier into qVFamTensorBlock.  Given these
embeddings, the S963 projection triple and the S951 transfer are constructed.
No fake projection or fake linearity is added.

The actual qVFam-to-L-valued map x ↦ x ⊗ 1 is recorded as the opposite
direction; it is not a projection to qVFam. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S969IndCarrierEmbeddingActual

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
open LeanFormal.IUT.XiFPaper.S963ActualToBlockProjectionActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe ua uv upi ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact embedding data: additive injections from the actual Ind carriers. -/
structure S969IndCarrierEmbeddingData
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v) where
  toBlock1 : S951Ind1Carrier (A := A) (C := C) j vQ P → qVFamTensorBlock T b
  toBlock2 : S951Ind2Carrier (C := C) j vQ → qVFamTensorBlock T b
  toBlock3 : S951Ind3Carrier (I := I) v m → qVFamTensorBlock T b
  map_add1 : ∀ x y, toBlock1 (x + y) = toBlock1 x + toBlock1 y
  map_add2 : ∀ x y, toBlock2 (x + y) = toBlock2 x + toBlock2 y
  map_mul3 : ∀ x y, toBlock3 (x * y) = toBlock3 x + toBlock3 y
  inj1 : Function.Injective toBlock1
  inj2 : Function.Injective toBlock2
  inj3 : Function.Injective toBlock3

/-- Exact embedding data gives the S963 projection triple. -/
noncomputable def s969ProjectionTriple_of_embeddings
    {j : Fin (capsuleLevels l)} {vQ : C.VQ}
    {P : PrcAutomorphism A j} {f : Capsule j.val → Realˣ}
    {v : V} {m : Int}
    {g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v}
    (E : S969IndCarrierEmbeddingData (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) j vQ P f v m g) :
    S963IndProjectionTriple (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) j vQ P f v m g where
  toBlock1 := E.toBlock1
  toBlock2 := E.toBlock2
  toBlock3 := E.toBlock3

/-- Exact embedding data yields the S951 transfer obligation. -/
theorem s969ActualIndImageTransferRequired_of_embeddings
    (h : ∃ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
      (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
      (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v),
      Nonempty (S969IndCarrierEmbeddingData (l := l) (V := V) (I := I)
        (A := A) (C := C) (T := T) (b := b) j vQ P f v m g)) :
    ActualIndImageTransferRequired (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) b := by
  rcases h with ⟨j, vQ, P, f, v, m, g, ⟨E⟩⟩
  exact s963ActualIndImageTransferRequired_of_projections (l := l) (V := V) (I := I)
    (A := A) (C := C) (T := T) (b := b)
    ⟨j, vQ, P, f, v, m, g,
      ⟨s969ProjectionTriple_of_embeddings (l := l) (V := V) (I := I)
        (A := A) (C := C) (T := T) (b := b) E⟩⟩

/-- Exact minimal embedding requirement. -/
def S969IndCarrierEmbeddingRequired : Prop :=
  ∃ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v),
    Nonempty (S969IndCarrierEmbeddingData (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) j vQ P f v m g)

end LeanFormal.IUT.XiFPaper.S969IndCarrierEmbeddingActual

end
