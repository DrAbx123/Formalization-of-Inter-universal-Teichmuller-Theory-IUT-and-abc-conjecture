/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual
import tmp.sheaf.xif.paper.Mzk1GapStructuralConsequencesActual
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual

/-!
# A637 REGION NECESSITY SUMMARY (mainline)

Why the paper comparison region must depend on the triple and must leave the hull:

* `fixed_region_heightComparison_false`: with the actual hull interface
  (`scaleShift = id`) and a triple-independent region, the height comparison is FALSE
  (unbounded ABC heights vs a fixed log-volume);
* `gap1_needs_unbounded_volume`: any region satisfying Gap 1 must have arbitrarily large
  log-volume;
* `gap1_not_inside_hull`: Gap 1 is impossible for regions contained in the finite hull.

Consequently the canonical design (`tripleScale`/`paperComparisonRegion` with the two
explicit gap hypotheses) is the minimal stable shape; no object is changed and no gap is
claimed proved.  ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal
namespace IUT
namespace XiFPaper
namespace Mzk1RegionNecessitySummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1A618ScalingObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1GapStructuralConsequencesActual
open Mzk1LanaBridgeAuditActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- With `scaleShift = id` and the triple-independent unit region, the height
  comparison fails for every `ε`. -/
theorem fixed_region_heightComparison_false (epsilon : ℝ) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (s1902LogVolume T (s1902UnitRegion T)).toReal) :=
  identity_scaleShift_obstruction T epsilon

/-- Any region satisfying Gap 1 must have arbitrarily large log-volume. -/
theorem gap1_needs_unbounded_volume {X : Type*} (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (h : Mzk1LanaBridgeAuditActual.Gap1Prop W region) :
    ∀ B : ℝ, ∃ a b c : Nat, IsABCTriple a b c ∧
      B < (W.logVolume (region a b c)).toReal :=
  gap1_forces_unbounded_regionVolume W region h

/-- Gap 1 cannot hold for regions contained in the finite hull. -/
theorem gap1_not_inside_hull {X : Type*} (W : IQHullLogVolumeInterface X)
    (hfin : W.logVolume W.hull < ⊤) (region : Nat → Nat → Nat → Set X)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    ¬ Mzk1LanaBridgeAuditActual.Gap1Prop W region :=
  gap1_impossible_of_region_in_finite_hull W hfin region hsub

/-- Audit rows for the region-necessity summary. -/
def regionNecessityRows : List (String × String) :=
  [ ("fixed scaleShift = id, triple-independent region", "height comparison FALSE"),
    ("Gap 1 holding", "region log-volume unbounded above"),
    ("region inside finite hull", "Gap 1 impossible"),
    ("consequence", "triple-dependent region required (tripleScale)"),
    ("scope", "structural facts only; gaps NOT proved; ABC gate NOT passed") ]

theorem regionNecessityRows_length : regionNecessityRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryActual

end
/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryActual.fixed_region_heightComparison_false
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryActual.gap1_needs_unbounded_volume
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryActual.gap1_not_inside_hull