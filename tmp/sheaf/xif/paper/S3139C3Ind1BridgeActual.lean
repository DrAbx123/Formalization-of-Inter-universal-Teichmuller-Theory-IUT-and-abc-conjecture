import tmp.sheaf.xif.paper.S3139FirstTriangleFieldACResidualActual
import tmp.sheaf.xif.paper.Ind1AutomorphismTensorActionActual
import tmp.sheaf.xif.paper.MultiradialProcessionActual
import tmp.sheaf.xif.paper.S3139FirstTriangleFieldBActual
import tmp.sheaf.xif.paper.S3139FieldCConjugateActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceLGPMonoidLayer
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 600000

/-!
# S3139: C3 — the (Ind1) bridge dependency is satisfied; the convention identification is the exact residual

C3 of the first-triangle residual is the (Ind1) convention bridge between the
contract poly-isomorphism action and the actual procession-automorphism reindex
action (IUT III:604-620, Fig. I.4-I.6).  This file:

* DISCHARGES the dependency `SourceInd1BridgeDependency` at the
  source-anchored real model: the standard source capsule data
  (`sourceCapsuleSourceDataStandard`) supplies the field-(A) source data, so
  `sourceInd1BridgeDependency_Real_holds` is a theorem;
* records the remaining exact identification
  `SourceInd1ConventionIdentification`: for every capsule level and every
  procession automorphism there is a linear comparison (a position-permutation
  convention change) carrying the polyIso pure-tensor image to the reindex
  pure-tensor image.  The two conventions differ (the polyIso action relabels
  in place, the procession action reindexes positions), so this comparison is
  a genuine one-line datum, not derivable from the pairing theorem (which lives
  on the Kummer layer) nor from the archimedean channel.
* fixes the polyIso built from a procession permutation
  (`polyIsoOfPerm`) so the residual statement is type-correct and downstream
  consumers can supply the bridge.

**Component, not paper object.**  Named consumers: the first-triangle mutation
and the lattice/mainline q/Theta comparison.  No sorry/axiom/True/PUnit/toy.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual
open LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- C3 dependency discharged at the source-anchored real model: the field-(A)
source capsule data is inhabited (standard source-anchored model). -/
theorem sourceInd1BridgeDependency_Real_holds
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceInd1BridgeDependency.{ua, uv, upi, umon, ui, 0, 0, 0, 0}
      Real l V I :=
  ⟨sourceCapsuleSourceDataStandard I⟩

/-- The poly-isomorphism action built from a procession permutation: it
relabels in place with the inverse permutation and trivial shell equivalences
(the shells of the standard real log-shell family are all the same). -/
def polyIsoOfPerm
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) :
    PolyIsoAction (standardRealLogShellFamily j.val) where
  labelPerm := P.perm.symm
  shellEquiv := fun i vQ v => LinearEquiv.refl Real _

/-- The exact remaining (Ind1) convention identification: for every capsule
level and procession automorphism, a linear comparison between the two
pure-tensor conventions.  This is the one-line datum left by C3 (page refs:
IUT III:604-620, Fig. I.4-I.6; the paper's identification of the
poly-isomorphism action with the Frobenius/procession action on the tensor
packets).  Not derivable from the Kummer-layer pairing theorem; recorded as
data, not assumed. -/
def SourceInd1ConventionIdentification
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) : Prop :=
  ∀ (j : Fin (capsuleLevels l)) (P : PrcAutomorphism A j),
    ∃ (Φ : (⨂[Real] i : Capsule j.val,
          DirectSumFactor (standardRealLogShellFamily j.val) () (P.perm.symm i))
        ≃ₗ[Real] (⨂[Real] i : Capsule j.val,
          DirectSumFactor (standardRealLogShellFamily j.val) () (P.perm.symm i))),
      ∀ (x : (i : Capsule j.val) →
          DirectSumFactor (standardRealLogShellFamily j.val) () i),
        Φ ((polyIsoOfPerm A j P).tensorMap ()
            (PiTensorProduct.tprod Real x)) =
          PrcAutomorphismTensorAction A (sourceRealCapsuleContract I) j ()
            P (PiTensorProduct.tprod Real x)

end LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual

end
