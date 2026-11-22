import tmp.sheaf.xif.paper.S3139RouteComparisonInvarianceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: route comparison-invariance consumer (FT.route.comparison-invariance)

Route-level consumer: with the comparison-invariance hypothesis explicitly
supplied, the V2-shaped comparison region's log-volume is convention-neutral;
this is the exact volume statement the paper route needs to import the C3
equality form into Cor312EpsilonArithmeticComparisonV2.comparisonRegion.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteComparisonInvarianceConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionClosureActual
open LeanFormal.IUT.XiFPaper.S3139ComparisonRegionV2NeutralActual
open LeanFormal.IUT.XiFPaper.S3139RouteComparisonInvarianceActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The route's exact volume-neutrality statement: with comparison invariance,
the V2 comparison region and its comparison image have the same log-volume. -/
theorem sourceV2ComparisonRegion_volume_neutral
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) (R : SourceV2ComparisonRegion I A j P)
    (volume : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i) → ℝ)
    (h : SourceRouteComparisonInvariance I A j P volume) (a b c : Nat) :
    volume ((sourceInd1ConventionComparison A j P) '' R.comparisonRegion a b c) =
      volume (R.comparisonRegion a b c) :=
  sourceRouteComparisonInvariance_region_volume I A j P R volume h a b c

end LeanFormal.IUT.XiFPaper.S3139RouteComparisonInvarianceConsumerActual

end
