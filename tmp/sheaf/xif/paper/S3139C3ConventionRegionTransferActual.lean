import tmp.sheaf.xif.paper.S3139C3ConventionRegionConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: C3 convention — region-transfer consumer for the source-side comparison region

If a source-side region/readout predicate on the tensor power is invariant under
the explicit comparison automorphism of the C3 closure, then membership
transfers between the two pure-tensor conventions (polyIso in-place vs
procession reindex).  This is the precise entry point for
Cor312EpsilonArithmeticComparisonV2.comparisonRegion: regions described by
comparison-invariant conditions are convention-neutral.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C3ConventionRegionTransferActual

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
open LeanFormal.IUT.XiFPaper.S3139C3ConventionRegionConsumerActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- Region transfer: for a comparison-invariant region predicate, the procession
reindex image lies in the region iff the polyIso in-place image does. -/
theorem sourceConventionRegion_transfer
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i)
    (S : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i))
    (hS : ∀ z : (⨂[Real] i : Capsule j.val, conventionFiber A j P i),
      z ∈ S ↔ (sourceInd1ConventionComparison A j P) z ∈ S) :
    PrcAutomorphismTensorAction A (sourceRealCapsuleContract I) j () P
        (PiTensorProduct.tprod Real x) ∈ S ↔
      (polyIsoOfPerm A j P).tensorMap ()
        (PiTensorProduct.tprod Real x) ∈ S := by
  rw [sourceInd1Convention_reindex_image]
  exact (hS _).symm

end LeanFormal.IUT.XiFPaper.S3139C3ConventionRegionTransferActual

end
