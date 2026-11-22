import tmp.sheaf.xif.paper.S3139C3ConventionClosureActual
import tmp.sheaf.xif.paper.S3139C3ConventionTheoremActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: C3 convention theorem — consumer form for the paper route's source-side region

Exposes the C3 convention identification in the equality form the paper route's
source-side q/Theta comparison region needs: the procession reindex image of a
pure tensor equals the explicit target-side comparison applied to the polyIso
in-place image.  Consumers defining source-side data through one convention can
transport it to the other along the explicit comparison.

**Component, not paper object.**  Registry frozen (final status/ledger only).
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C3ConventionRegionConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionTheoremActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionClosureActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The explicit commuting square (equality form) for consumers: the procession
reindex image of a pure tensor is the explicit comparison applied to the
polyIso in-place image. -/
theorem sourceInd1Convention_reindex_image
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    PrcAutomorphismTensorAction A (sourceRealCapsuleContract I) j () P
        (PiTensorProduct.tprod Real x) =
      (sourceInd1ConventionComparison A j P)
        ((polyIsoOfPerm A j P).tensorMap ()
          (PiTensorProduct.tprod Real x)) := by
  rw [PrcAutomorphismTensorAction_tprod, polyIsoOfPerm_tensorMap_tprod]
  have h := sourceInd1ConventionComparison_tprod A j P
    (fun i => (show conventionFiber A j P i from x i))
  exact h.symm

end LeanFormal.IUT.XiFPaper.S3139C3ConventionRegionConsumerActual

end
