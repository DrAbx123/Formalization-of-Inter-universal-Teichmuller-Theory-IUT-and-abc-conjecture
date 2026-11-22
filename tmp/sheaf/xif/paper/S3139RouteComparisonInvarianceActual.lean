import tmp.sheaf.xif.paper.S3139ComparisonRegionV2NeutralActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: route comparison-invariance hypothesis (mainline exact shape, FT.route.comparison-invariance)

Mainline's answer (FINAL-STATUS A22): the route's comparisonRegion consumes the
C3 equality form through the comparison-neutral region image, AND requires an
explicit comparison-invariance hypothesis -- the linear automorphism gives NO
automatic log-volume invariance.  Exact shape proposed by mainline:

  S3131RouteComparisonInvarianceHypothesis (W) (phi : X -> X) :=
    forall S, W.logVolume (phi '' S) = W.logVolume S

This file records the hypothesis in that exact shape, instantiated on the
source-side V2-shaped comparison region, and derives the volume-neutrality
statements the route needs.  The hypothesis itself is the named route residual
FT.route.comparison-invariance (owner mainline); it is NOT assumed anywhere
without being passed explicitly.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteComparisonInvarianceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionClosureActual
open LeanFormal.IUT.XiFPaper.S3139ComparisonRegionV2NeutralActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- Mainline's route comparison-invariance hypothesis, instantiated on the
source-side tensor power: the log-volume functional is invariant under the
explicit C3 comparison map on every region. -/
def SourceRouteComparisonInvariance
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (volume : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i) → ℝ) :
    Prop :=
  ∀ S : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i),
    volume ((sourceInd1ConventionComparison A j P) '' S) = volume S

/-- The invariance hypothesis gives volume-neutrality of any region image under
the comparison map (the route's needed statement). -/
theorem SourceRouteComparisonInvariance.volume_image
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (volume : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i) → ℝ)
    (h : SourceRouteComparisonInvariance I A j P volume)
    (S : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i)) :
    volume ((sourceInd1ConventionComparison A j P) '' S) = volume S :=
  h S

/-- With the invariance hypothesis, the volume of every V2-shaped comparison
region is equal to the volume of its comparison image -- the convention-neutral
volume statement the route consumes. -/
theorem sourceRouteComparisonInvariance_region_volume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) (R : SourceV2ComparisonRegion I A j P)
    (volume : Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i) → ℝ)
    (h : SourceRouteComparisonInvariance I A j P volume) (a b c : Nat) :
    volume ((sourceInd1ConventionComparison A j P) '' R.comparisonRegion a b c) =
      volume (R.comparisonRegion a b c) :=
  h (R.comparisonRegion a b c)

end LeanFormal.IUT.XiFPaper.S3139RouteComparisonInvarianceActual

end
