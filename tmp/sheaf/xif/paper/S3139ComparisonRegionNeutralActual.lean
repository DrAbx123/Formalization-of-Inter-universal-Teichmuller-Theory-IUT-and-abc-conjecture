import tmp.sheaf.xif.paper.S3139C3ConventionRegionTransferActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: C3 integration — convention-neutral source-side comparison region

Bundles a source-side region on the permuted-family tensor power with the
comparison-invariance condition, and derives the convention-transfer of region
membership.  This is the C3-closure entry shape for the paper route:
Cor312EpsilonArithmeticComparisonV2.comparisonRegion data that is
comparison-invariant is convention-neutral on the source side.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139ComparisonRegionNeutralActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionClosureActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionRegionConsumerActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- A convention-neutral source-side comparison region: a region on the
permuted-family tensor power invariant under the explicit C3 comparison
automorphism. -/
structure SourceConventionNeutralRegion
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) where
  /-- the region on the permuted-family tensor power -/
  region : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i)
  /-- invariance under the explicit C3 comparison automorphism -/
  neutral : ∀ z,
    z ∈ region ↔ (sourceInd1ConventionComparison A j P) z ∈ region

/-- For a convention-neutral region, membership transfers between the polyIso
in-place convention and the procession reindex convention. -/
theorem SourceConventionNeutralRegion.mem_transfer
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) (R : SourceConventionNeutralRegion I A j P)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    PrcAutomorphismTensorAction A (sourceRealCapsuleContract I) j () P
        (PiTensorProduct.tprod Real x) ∈ R.region ↔
      (polyIsoOfPerm A j P).tensorMap ()
        (PiTensorProduct.tprod Real x) ∈ R.region := by
  rw [sourceInd1Convention_reindex_image]
  exact (R.neutral _).symm

end LeanFormal.IUT.XiFPaper.S3139ComparisonRegionNeutralActual

end
