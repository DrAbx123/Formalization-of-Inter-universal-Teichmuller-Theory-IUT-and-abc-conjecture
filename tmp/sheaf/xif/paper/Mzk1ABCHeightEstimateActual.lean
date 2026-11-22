/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import Mathlib.Tactic

/-!
# ABC height estimate from the ABC-frontier height-comparison clause

This file consumes the existing ABCBridge frontier clause
`FrontierHeightComparisonClause` (ABCBridge/Bridge/ABCFrontier.lean:146) and turns it
into the exact hheight hypothesis consumed by the Stage-5 numerical reduction
`abcConjecture_of_literalLogVolumeEstimates`.

The fixed point datum `x` keeps the comparison region independent of epsilon except
through the clause's own epsilon; the region still varies with the triple (as it
must: `no_constantRegion_heightComparison` shows a triple-independent region cannot
bound unbounded heights).  No clause is proved here; the two frontier clauses are
the open arithmetic content (IUT IV section 2).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCHeightEstimateActual

open LeanFormal.IUT

universe u

/-- The triple-dependent normalized region log-volume used as the ABC height
readout function: `logVolume a b c = (W.logVolume (region at x a b c)).toReal`.
The region is the concrete Set-level `normalizedComparisonRegion`; it varies with
the triple through `x`. -/
noncomputable def frontierRegionLogVolume {X : Type u}
    (W : IQHullLogVolumeInterface X) (x : Nat → Nat → Nat → X) (a b c : Nat) : ℝ :=
  (W.logVolume (normalizedComparisonRegion W x a b c)).toReal

/-- **Height estimate** from the existing frontier height-comparison clause, in
the exact shape required by `abcConjecture_of_literalLogVolumeEstimates`. -/
theorem abcHeightEstimate_of_frontierHeightComparison {X : Type u}
    (W : IQHullLogVolumeInterface X) (x : Nat → Nat → Nat → X)
    (h : FrontierHeightComparisonClause W (fun _ _ => x)) :
    ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + δ) * frontierRegionLogVolume W x a b c := by
  intro δ hδ a b c habc
  simpa only [frontierRegionLogVolume] using h δ hδ a b c habc

/-- Bundled form of the height-estimate predicate. -/
def ABCHeightEstimate {X : Type u} (W : IQHullLogVolumeInterface X)
    (x : Nat → Nat → Nat → X) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + δ) * frontierRegionLogVolume W x a b c

theorem abcHeightEstimate_of_frontierHeightComparison' {X : Type u}
    (W : IQHullLogVolumeInterface X) (x : Nat → Nat → Nat → X)
    (h : FrontierHeightComparisonClause W (fun _ _ => x)) :
    ABCHeightEstimate W x :=
  abcHeightEstimate_of_frontierHeightComparison W x h

end LeanFormal.IUT.XiFPaper.Mzk1ABCHeightEstimateActual

end