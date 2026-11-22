import tmp.sheaf.xif.paper.S3139FirstTriangleMutationActual
import tmp.sheaf.xif.paper.S3139StageOneSeamsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: first-triangle residual decomposition (minimal data fields)

The actual first-triangle mutation is constructed in
`S3139FirstTriangleMutationActual` from three supplied data structures.  This
file records the minimal residual data demands of the first triangle with their
paper locations, closes the task-9 `SourceMultiradialMutationDemand` at its
stated etale-like-portion level, and proves the actual Ind1/Ind2
non-interference law on pure tensors.

Residual fields (each is a concrete existence statement about actual
structures, not an arbitrary proposition):

1. `SourceLogShellContractMissing`: log-shell modules over the places, the
   capsule prime-strip procession and the poly-isomorphism action
   (IUT III:584-606, 663-668; Formalization of IUT (2026-04) :514-524).
2. `SourceLGPDataMissing`: the LGP splitting-monoid carrier, its theta-value
   generated splitting monoid, and its action on the tensor packets
   (III:610-615, Fig. I.4; Formalization :507-513).
3. `SourceFmodRealAlgebraMissing`: a Real embedding of the actual source
   `F_mod`, needed to feed the actual source units into the Real-valued (Ind2)
   copy action (III:616-620, Fig. I.5).

Still not a single Lean structure: the (Ind1) identification of the contract's
poly-isomorphism action with the actual procession-automorphism action, and the
(Ind3) log-Kummer compatibility (III:669-685, 710-729), both of which require
the bridge data of (1).  No sorry/axiom/True/PUnit/toy carrier.

**Component, not paper object.**  These are the minimal prerequisite data
fields of the first-triangle paper object, with page refs; named future
consumer: @S3139FirstTriangleMutationActual@ + the paper first triangle.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleResidualActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.S3139SourceBPSActual
open LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual
open LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual.SourceEtHT
open LeanFormal.IUT.XiFPaper.S3139StageOneSeamsActual
open scoped TensorProduct

universe ua uv upi umon ui uR uVQ uPlace uShell uM

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (D : SourceLGPData.{uM, 0, uVQ, uPlace, uShell, uv, ua, upi, umon, ui}
  Real l V I)
variable (φ : SourceFmodRealEmbedding (I := I))
variable (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ)

/-! ## 1. Minimal residual data demands -/

/-- Residual field 1: the log-shell capsule contract for the actual source.
IUT III:584-606, 663-668; Formalization of IUT (2026-04) :514-524. -/
def SourceLogShellContractMissing (R : Type uR) [CommSemiring R]
    (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, uR, uVQ,
    uPlace, uShell} R l V I)

/-- Residual field 2: the LGP splitting-monoid data and its action on the
tensor packets.  IUT III:610-615, Fig. I.4; Formalization :507-513. -/
def SourceLGPDataMissing (R : Type uR) [CommSemiring R]
    (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (SourceLGPData.{uM, uR, uVQ, uPlace, uShell, uv, ua, upi, umon,
    ui} R l V I)

/-- Residual field 3: a Real embedding of the actual source `F_mod`, needed for
the Real-valued (Ind2) copy action.  IUT III:616-620, Fig. I.5. -/
def SourceFmodRealAlgebraMissing
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (SourceFmodRealEmbedding (I := I))

/-! ## 2. Closing the task-9 demand at the etale-like-portion level -/

/-- The task-9 `SourceMultiradialMutationDemand` is met at its stated level by
the actual gluing: for the canonical BPS and the 0-column etHT the etale-like
portions `G_v` coincide, so its mutation field is the identity. -/
noncomputable def sourceMultiradialMutationDemandInhabitant
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceMultiradialMutationDemand J (sourceBPSOfTheater J 0 0)
      (sourceEtHTZeroColumn J 0) where
  bps_glued := ⟨SourceFTimesMuPrimeStripEquivalence.refl _⟩
  etHT_zero_column := rfl
  mutation := fun _ x => x

/-- The 0-column etHT's etale-like portion is the canonical BPS's: the radial
target and the stage-1 input share the actual `G_v` data. -/
theorem sourceEtHTTarget_eq_bpsEtaleLikePortion
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) :
    (sourceEtHTZeroColumn J 0).etaleLikePortion v =
      (sourceBPSOfTheater J 0 0).etaleLikePortion v := rfl

/-! ## 3. Ind1/Ind2 non-interference on pure tensors -/

/-- (Ind1)/(Ind2) non-interference (IUT III:710-729): acting by a procession
automorphism (Ind1) after the independent `F_mod^x` copies (Ind2) is the same
as applying the relabeled copies on the reindexed tensor factors. -/
theorem ind1_ind2_tprod_commute (P : PrcAutomorphism A j)
    (f : SourceFmodUnitCopies (I := I) j)
    (x : (i : Capsule j.val) → DirectSumFactor (D.capsule.logShell j) vQ i) :
    PrcAutomorphismTensorAction A D.capsule j vQ P
        (sourceInd2RealTensorEquiv D.capsule j vQ φ f
          (PiTensorProduct.tprod Real x)) =
      PiTensorProduct.tprod Real
        (fun i => ind2FactorAction (C := D.capsule) (j := j) (vQ := vQ)
          (Units.map φ.toMonoidHom (f (P.perm.symm i))) (P.perm.symm i)
          (x (P.perm.symm i))) := by
  rw [sourceInd2RealTensorEquiv_tprod, PrcAutomorphismTensorAction_tprod]

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleResidualActual

end
