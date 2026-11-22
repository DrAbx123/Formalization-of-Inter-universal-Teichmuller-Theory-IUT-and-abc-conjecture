import tmp.sheaf.xif.paper.S969IndCarrierEmbeddingActual
import tmp.sheaf.xif.paper.PaperFinalLValuedTensorCarrierActual

/-! # S972: exact type conditions for the Ind-carrier embeddings

The actual qVFam-to-L-valued map is x ↦ x ⊗ 1; it has the wrong direction and
there is no canonical projection from the L-valued tensor product back to
qVFamTensorBlock.  The Ind carriers are Real-vector spaces and qVFamTensorBlock
is a Qp-vector space; no field embedding Qp -> Real exists and no canonical
Qp-linear map Real -> Qp exists.

Hence the exact minimal type condition is an additive injection (not a
Qp-linear map) from each actual Ind carrier into qVFamTensorBlock.  This file
records that condition and constructs S969's embedding data from it; no
projection or linearity is fabricated. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S972IndAdditiveEmbeddingConditionsActual

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
open LeanFormal.IUT.XiFPaper.S969IndCarrierEmbeddingActual
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

/-- Exact type condition: additive injections from the three actual carriers.
Ind3 carries a group structure, so its compatibility is multiplicative-to-
additive. -/
structure S972IndAdditiveEmbeddingConditions
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

/-- The exact type conditions supply S969's embedding data. -/
noncomputable def s972EmbeddingData_of_conditions
    {j : Fin (capsuleLevels l)} {vQ : C.VQ}
    {P : PrcAutomorphism A j} {f : Capsule j.val → Realˣ}
    {v : V} {m : Int}
    {g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v}
    (E : S972IndAdditiveEmbeddingConditions (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) j vQ P f v m g) :
    S969IndCarrierEmbeddingData (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) j vQ P f v m g where
  toBlock1 := E.toBlock1
  toBlock2 := E.toBlock2
  toBlock3 := E.toBlock3
  map_add1 := E.map_add1
  map_add2 := E.map_add2
  map_mul3 := E.map_mul3
  inj1 := E.inj1
  inj2 := E.inj2
  inj3 := E.inj3

/-- Exact minimal requirement: the additive embedding conditions. -/
def S972IndAdditiveEmbeddingRequired : Prop :=
  ∃ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) (f : Capsule j.val → Realˣ)
    (v : V) (m : Int) (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v),
    Nonempty (S972IndAdditiveEmbeddingConditions (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) j vQ P f v m g)

/-- The exact type condition yields S969's exact requirement. -/
theorem s969IndCarrierEmbeddingRequired_of_conditions
    (h : S972IndAdditiveEmbeddingRequired (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b)) :
    S969IndCarrierEmbeddingRequired (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) := by
  rcases h with ⟨j, vQ, P, f, v, m, g, ⟨E⟩⟩
  exact ⟨j, vQ, P, f, v, m, g,
    ⟨s972EmbeddingData_of_conditions (l := l) (V := V) (I := I)
      (A := A) (C := C) (T := T) (b := b) E⟩⟩

/-- Actual qVFam-to-L-valued map exists with the opposite direction. -/
noncomputable def s972QVFamToLValued :
    qVFamTensorBlock T b → FinalLValuedCarrier T b :=
  qVFamToLValued (l := l) T b

end LeanFormal.IUT.XiFPaper.S972IndAdditiveEmbeddingConditionsActual

end
