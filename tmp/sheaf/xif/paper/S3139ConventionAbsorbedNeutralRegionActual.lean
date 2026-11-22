import tmp.sheaf.xif.paper.S3139ComparisonRegionNeutralActual
import tmp.sheaf.xif.paper.S3139RouteComparisonInvarianceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: convention choice absorbed by a neutral invariant region

Adapted from vendor promachina Iut/Stage1/IUTStage1FrobenioidShift.lean:92
structure IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice: for a
comparison-neutral source-side region together with the explicit
comparison-invariance hypothesis, the log-volume readout is independent of the
C3 convention choice.  This packages the two ingredients the paper route needs
into one capstone statement (both are explicit hypotheses, never hidden).

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139ConventionAbsorbedNeutralRegionActual

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
open LeanFormal.IUT.XiFPaper.S3139ComparisonRegionNeutralActual
open LeanFormal.IUT.XiFPaper.S3139RouteComparisonInvarianceActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- Capstone: a comparison-neutral region plus the explicit comparison-invariance
hypothesis makes the region's log-volume readout independent of the convention
choice, and membership transfers between the two conventions. -/
theorem sourceConvention_absorbed_by_neutral_invariant_region
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (R : SourceConventionNeutralRegion I A j P)
    (volume : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i) → ℝ)
    (h : SourceRouteComparisonInvariance I A j P volume)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    (PrcAutomorphismTensorAction A (sourceRealCapsuleContract I) j () P
        (PiTensorProduct.tprod Real x) ∈ R.region ↔
      (polyIsoOfPerm A j P).tensorMap ()
        (PiTensorProduct.tprod Real x) ∈ R.region) ∧
      volume ((sourceInd1ConventionComparison A j P) '' R.region) =
        volume R.region :=
  ⟨R.mem_transfer I A j P x, h R.region⟩

end LeanFormal.IUT.XiFPaper.S3139ConventionAbsorbedNeutralRegionActual

end
