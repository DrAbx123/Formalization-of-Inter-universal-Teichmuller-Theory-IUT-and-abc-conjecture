import tmp.sheaf.xif.paper.S3139FirstTriangleFieldBActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: fields (A) and (C) refined; final first-triangle residual

Field (A): the capsule contract is now decomposed into the part that is
constructible (the actual source procession, constructed in
`S3139FirstTriangleFieldBActual` as `Procession.ofOriginalInput`) and the
exact remaining source data `SourceCapsuleSourceDataMissing`: the valuation and
place types together with the log-shell module family and the
poly-isomorphism action (IUT III:584-606, 663-668; Formalization of IUT
(2026-04) :514-524).  `sourceCapsuleContractOfSourceData` assembles the contract
from that data with the actual procession, so the field is now exactly the
paper's missing log-shell/place data rather than the whole contract.

Field (C): the Real ring embedding `F_mod -> R` used in the task-23 mutation is
reclassified (per the team methodology note) as a *modeling convention*, not a
paper object: the paper's copies act through the conjugate action on local
units/log-shells (III:616-620, Fig. I.5), not through a global real embedding.
The paper-faithful data are recorded exactly as
`SourceInd2CopyActionData` (a group action of the copy family on the tensor
packet preserving the splitting-monoid scalar action); the Real-embedding
instance `sourceInd2CopyActionDataOfRealEmbedding` shows that the modeling
bridge supplies such data.  A negative result about Real embeddings (e.g. for
the Gaussian example field) is a model/convention mismatch and is therefore
not promoted; it is recorded in the ledger as negative only.

**Component, not paper object.**  Named future consumer: the first-triangle
paper object (BPS -> multiradial representation) and the lattice/mainline
q/Theta comparison.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleMutationActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleResidualActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open scoped TensorProduct

universe ua uv upi umon ui uR uVQ uPlace uShell uC

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Field (A): the exact remaining source log-shell data -/

/-- The exact remaining source data of the log-shell capsule contract: the
valuation and place types, the log-shell module family, and the
poly-isomorphism action.  The actual procession is *not* part of this missing
data (it is constructed from the original input in
`S3139FirstTriangleFieldBActual`).  IUT III:584-606, 663-668; Formalization
2026-04 :514-524. -/
structure SourceCapsuleSourceDataMissing (R : Type uR) [CommSemiring R]
    (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  VQ : Type uVQ
  place : VQ → Type uPlace
  [fintypePlace : ∀ vQ, Fintype (place vQ)]
  logShell : (j : Fin (capsuleLevels l)) →
    LogShellFamily.{uR, uVQ, uPlace, uShell} R place j.val
  polyIso : (j : Fin (capsuleLevels l)) →
    PolyIsoAction.{uR, uVQ, uPlace, uShell} (logShell j)

attribute [instance] SourceCapsuleSourceDataMissing.fintypePlace

/-- Assemble the capsule contract from the missing source log-shell data and
the *constructed* actual procession. -/
def sourceCapsuleContractOfSourceData (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (S : SourceCapsuleSourceDataMissing R l V I) :
    SourceProcessionCapsuleContract R l V I where
  procession := Procession.ofOriginalInput I 0 0
  VQ := S.VQ
  place := S.place
  fintypePlace := S.fintypePlace
  logShell := S.logShell
  polyIso := S.polyIso

/-- The one-point standard-real model data: the finite-model log-shell layer.
This shows the decomposition is inhabited and matches
`sourceRealCapsuleContract`. -/
def sourceCapsuleSourceDataStandard (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceCapsuleSourceDataMissing.{ua, uv, upi, umon, ui, 0, 0, 0, 0}
      Real l V I where
  VQ := Unit
  place := fun _ => Unit
  fintypePlace := fun _ => inferInstance
  logShell := fun j => standardRealLogShellFamily j.val
  polyIso := fun j => PolyIsoAction.refl (standardRealLogShellFamily j.val)

/-! ## 2. Field (C): the paper-faithful (Ind2) copy-action data -/

/-- The paper-faithful (Ind2) copy action data (IUT III:616-620, Fig. I.5): a
group of copies acting on the tensor packet by linear automorphisms that
preserve the splitting-monoid scalar action.  This is the exact shape needed by
the mutation's (Ind2) slot; the Real ring embedding of the task-23 formulation
is only one model supplying it. -/
structure SourceInd2CopyActionData (R : Type uR) [CommSemiring R]
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (D : SourceLGPData R l V I)
    (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ)
    (Copies : Type uC) [Group Copies] where
  /-- the copy action on the tensor packet -/
  action : Copies → (D.tensorPacket j vQ ≃ₗ[R] D.tensorPacket j vQ)
  /-- the unit copy acts by the identity -/
  action_one : action 1 = LinearEquiv.refl R (D.tensorPacket j vQ)
  /-- composition of copies -/
  action_mul : ∀ c d : Copies, action (c * d) = (action d).trans (action c)
  /-- the copy action preserves the splitting-monoid scalar action -/
  action_scalar : ∀ (c : Copies) (g : D.lgp.Carrier)
    (x : D.tensorPacket j vQ),
    action c ((D.actionOnTensorPacket j vQ) g x) =
      (D.actionOnTensorPacket j vQ) g (action c x)

/-- The Real-embedding *model* supplies the paper-faithful copy-action data
shape: the copies are the actual @F_mod^x@ unit families acting through the
actual source-unit Ind2 action (the generic action laws are transported through
the algebra structure induced by the embedding).  This shows that the Real
embedding is a modeling bridge for the same data shape, not the paper object
itself. -/
noncomputable def sourceInd2CopyActionDataOfRealEmbedding
    (D : SourceLGPData Real l V I) (φ : SourceFmodRealEmbedding (I := I))
    (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ) :
    SourceInd2CopyActionData Real D j vQ
      (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ) where
  action := by
    letI : Algebra (I.initial.arithmetic.Fmod) Real := RingHom.toAlgebra φ
    exact fun f => sourceInd2TensorEquiv (I := I) (R := Real) D.capsule j vQ f
  action_one := by
    letI : Algebra (I.initial.arithmetic.Fmod) Real := RingHom.toAlgebra φ
    exact sourceInd2TensorEquiv_one (I := I) (R := Real) D.capsule j vQ
  action_mul := by
    letI : Algebra (I.initial.arithmetic.Fmod) Real := RingHom.toAlgebra φ
    intro c d
    exact sourceInd2TensorEquiv_mul (I := I) (R := Real) D.capsule j vQ c d
  action_scalar := by
    letI : Algebra (I.initial.arithmetic.Fmod) Real := RingHom.toAlgebra φ
    intro c g x
    show sourceInd2TensorEquiv (I := I) (R := Real) D.capsule j vQ c
        (((D.action j).scalar g) • x) =
      ((D.action j).scalar g) •
        (sourceInd2TensorEquiv (I := I) (R := Real) D.capsule j vQ c) x
    exact (sourceInd2TensorEquiv (I := I) (R := Real)
      D.capsule j vQ c).map_smul ((D.action j).scalar g) x

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual

end
