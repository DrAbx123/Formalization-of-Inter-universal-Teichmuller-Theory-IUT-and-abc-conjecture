import tmp.sheaf.xif.paper.S3139ComparisonRegionNeutralActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: V2-shaped convention-neutral comparison region (C3 integration)

Realizes the field shape of the route's per-epsilon comparison data
(Cor312EpsilonArithmeticComparisonV2.comparisonRegion : Nat -> Nat -> Nat -> Set X
with logShellPoint membership) on the source-side tensor power, together with
comparison-neutrality from the C3 closure.  Consumers of the route can use the
membership-transfer lemma to make their source-side region definition
convention-neutral.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139ComparisonRegionV2NeutralActual

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
open LeanFormal.IUT.XiFPaper.S3139ComparisonRegionNeutralActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The V2-shaped per-epsilon comparison region on the source-side tensor
power, with a comparison-neutral region condition. -/
structure SourceV2ComparisonRegion
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) where
  /-- the point-dependent comparison region (V2 field shape) -/
  comparisonRegion : Nat → Nat → Nat →
    Set (⨂[Real] i : Capsule j.val, conventionFiber A j P i)
  /-- the log-shell point of each triple -/
  logShellPoint : Nat → Nat → Nat →
    (⨂[Real] i : Capsule j.val, conventionFiber A j P i)
  /-- the log-shell point lies in the comparison region -/
  logShellPoint_mem : ∀ a b c : Nat,
    logShellPoint a b c ∈ comparisonRegion a b c
  /-- C3 comparison-neutrality of the region -/
  neutral : ∀ (a b c : Nat) (z : ⨂[Real] i : Capsule j.val, conventionFiber A j P i),
    z ∈ comparisonRegion a b c ↔
      (sourceInd1ConventionComparison A j P) z ∈ comparisonRegion a b c

/-- The convention-transfer of membership at a V2-shaped region point: the
procession reindex image of a pure tensor lies in the region iff the polyIso
in-place image does. -/
theorem SourceV2ComparisonRegion.mem_transfer
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) (R : SourceV2ComparisonRegion I A j P)
    (a b c : Nat)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    PrcAutomorphismTensorAction A (sourceRealCapsuleContract I) j () P
        (PiTensorProduct.tprod Real x) ∈ R.comparisonRegion a b c ↔
      (polyIsoOfPerm A j P).tensorMap ()
        (PiTensorProduct.tprod Real x) ∈ R.comparisonRegion a b c := by
  rw [sourceInd1Convention_reindex_image]
  exact (R.neutral a b c _).symm

/-- The neutral-region bundle yields a V2-shaped region with the same
point-membership data. -/
def SourceV2ComparisonRegion.ofNeutral
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (R : SourceConventionNeutralRegion I A j P)
    (point : Nat → Nat → Nat →
      (⨂[Real] i : Capsule j.val, conventionFiber A j P i))
    (hpoint : ∀ a b c, point a b c ∈ R.region) :
    SourceV2ComparisonRegion I A j P where
  comparisonRegion := fun _ _ _ => R.region
  logShellPoint := point
  logShellPoint_mem := hpoint
  neutral := fun _ _ _ z => R.neutral z

end LeanFormal.IUT.XiFPaper.S3139ComparisonRegionV2NeutralActual

end
