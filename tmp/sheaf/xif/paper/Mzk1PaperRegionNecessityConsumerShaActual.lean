import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual
import tmp.sheaf.xif.paper.Mzk1GapStructuralConsequencesActual
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import tmp.sheaf.xif.paper.Mzk1TripleDependentRegionAlignShaActual

/-!
# shehdd A639 paper-region-necessity consumer (Sha, read-only)

Green consumer assembling the paper-region-necessity audit from green sources:
* A618 obstruction (`scaleShift = id` + triple-independent unit region fails the
  height comparison) — re-exported;
* Gap 1 forces unbounded region log-volume;
* Gap 1 is impossible for a region contained in the finite hull;
* triple-dependent region alignment (paper shape).

Scope: gaps are NOT proved; this is an audit/consumer assembly only.  The canonical
`Mzk1PaperRegionNecessityFinalActual` is mainline-owned; this file is a read-only
Sha companion.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityConsumerShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1A618ScalingObstructionActual
open Mzk1GapStructuralConsequencesActual
open Mzk1LanaBridgeAuditActual

/-- A618 obstruction, re-exported for the audit consumer. -/
theorem consumer_identity_obstruction {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
    (epsilon : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (s1902LogVolume T (s1902UnitRegion T)).toReal) :=
  identity_scaleShift_obstruction T epsilon

/-- Gap 1 forces unbounded region log-volume (re-export). -/
theorem consumer_gap1_forces_unbounded {X : Type*}
    (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X) (h : Gap1Prop W region) :
    ∀ B : Real, ∃ a b c : Nat, IsABCTriple a b c ∧
      B < (W.logVolume (region a b c)).toReal :=
  gap1_forces_unbounded_regionVolume W region h

/-- Gap 1 is impossible inside the finite hull (re-export). -/
theorem consumer_gap1_impossible_in_finite_hull {X : Type*}
    (W : IQHullLogVolumeInterface X)
    (hfin : W.logVolume W.hull < ⊤)
    (region : Nat → Nat → Nat → Set X)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    ¬ Gap1Prop W region :=
  gap1_impossible_of_region_in_finite_hull W hfin region hsub

end LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityConsumerShaActual

/-! ### Axiom gates (read-only consumer) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityConsumerShaActual.consumer_identity_obstruction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityConsumerShaActual.consumer_gap1_forces_unbounded
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityConsumerShaActual.consumer_gap1_impossible_in_finite_hull
