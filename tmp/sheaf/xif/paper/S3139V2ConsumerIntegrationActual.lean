import tmp.sheaf.xif.paper.S3139ComparisonRegionV2NeutralActual
import tmp.sheaf.xif.paper.S3139RouteComparisonInvarianceActual
import tmp.sheaf.xif.paper.S3139ConventionAbsorbedNeutralRegionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: V2 comparison-region consumer integration (C3 closure + absorption capstone)

Integrates the certified C3 closure and the convention-absorption capstone into
the consumer path of mainline's V2 comparison region
(Cor312EpsilonArithmeticComparisonV2.comparisonRegion):
a V2-shaped comparison region with the explicit comparison-invariance hypothesis
yields both the convention membership transfer and the region-volume neutrality.
This is the exact consumer bundle agreed with mainline (FINAL-STATUS A22) and
abc (comparison-invariance honesty flag).

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139V2ConsumerIntegrationActual

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
open LeanFormal.IUT.XiFPaper.S3139ComparisonRegionV2NeutralActual
open LeanFormal.IUT.XiFPaper.S3139RouteComparisonInvarianceActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The V2 comparison-region consumer bundle: the V2-shaped region, its
log-volume readout, and the explicit comparison-invariance hypothesis. -/
structure SourceV2ComparisonRegionConsumer
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) where
  /-- the V2-shaped comparison region with the neutral condition -/
  region : SourceV2ComparisonRegion I A j P
  /-- the log-volume readout of regions -/
  volume : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i) → ℝ
  /-- FT.route.comparison-invariance (explicit residual) -/
  invariance : SourceRouteComparisonInvariance I A j P volume

/-- The V2 consumer path: for every triple and pure tensor, the comparison
membership transfers between conventions AND the region volume is
convention-neutral (given the explicit invariance hypothesis). -/
theorem SourceV2ComparisonRegionConsumer.membership_and_volume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) (C : SourceV2ComparisonRegionConsumer I A j P)
    (a b c : Nat)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    (PrcAutomorphismTensorAction A (sourceRealCapsuleContract I) j () P
        (PiTensorProduct.tprod Real x) ∈ C.region.comparisonRegion a b c ↔
      (polyIsoOfPerm A j P).tensorMap ()
        (PiTensorProduct.tprod Real x) ∈ C.region.comparisonRegion a b c) ∧
      C.volume ((sourceInd1ConventionComparison A j P) ''
        C.region.comparisonRegion a b c) =
        C.volume (C.region.comparisonRegion a b c) :=
  ⟨C.region.mem_transfer I A j P a b c x, C.invariance _⟩

end LeanFormal.IUT.XiFPaper.S3139V2ConsumerIntegrationActual

end
