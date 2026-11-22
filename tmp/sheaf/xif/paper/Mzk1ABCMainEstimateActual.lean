/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCHeightEstimateActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual
import Mathlib.Tactic

/-!
# ABC main estimate and the Stage-5 feed

Consumes the existing ABCBridge frontier region-comparison clause
`FrontierRegionComparisonClause` (ABCBridge/Bridge/ABCFrontier.lean:173) and the
height estimate from `Mzk1ABCHeightEstimateActual`, then feeds the Stage-5
numerical reduction `abcConjecture_of_literalLogVolumeEstimates`
(Mzk1IUTIVStage5NumericalActual) to derive `ABCConjecture` conditionally on the
two existing frontier clauses.

Both clauses are the open IUT IV section 2 arithmetic content; nothing is proved
here and no clause is weakened.  The hull volume is the interface's own hull
log-volume converted to Real.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCMainEstimateActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCHeightEstimateActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

universe u

/-- Hull log-volume read off the frontier interface. -/
noncomputable def frontierHullVolume {X : Type u}
    (W : IQHullLogVolumeInterface X) : ℝ :=
  (W.logVolume W.hull).toReal

/-- **Main log-volume estimate** from the existing frontier region-comparison
clause, in the exact shape required by `abcConjecture_of_literalLogVolumeEstimates`. -/
theorem abcMainEstimate_of_frontierRegionComparison {X : Type u}
    (W : IQHullLogVolumeInterface X) (x : Nat → Nat → Nat → X)
    (h : FrontierRegionComparisonClause W (fun _ _ => x)) :
    ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        frontierRegionLogVolume W x a b c ≤
          (1 + δ) * arithmeticWeight (abcRationalPoint a c) + frontierHullVolume W + D := by
  intro δ hδ
  obtain ⟨D, hD⟩ := h δ hδ
  exact ⟨D, fun a b c habc => by
    simpa only [frontierRegionLogVolume, frontierHullVolume] using hD a b c habc⟩

/-- Bundled form of the main-estimate predicate. -/
def ABCMainEstimate {X : Type u} (W : IQHullLogVolumeInterface X)
    (x : Nat → Nat → Nat → X) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
    ∀ a b c : Nat, IsABCTriple a b c →
      frontierRegionLogVolume W x a b c ≤
        (1 + δ) * arithmeticWeight (abcRationalPoint a c) + frontierHullVolume W + D

theorem abcMainEstimate_of_frontierRegionComparison' {X : Type u}
    (W : IQHullLogVolumeInterface X) (x : Nat → Nat → Nat → X)
    (h : FrontierRegionComparisonClause W (fun _ _ => x)) :
    ABCMainEstimate W x :=
  abcMainEstimate_of_frontierRegionComparison W x h

/-- **Stage-5 feed**: the two frontier clauses imply `ABCConjecture` through the
existing green numerical reduction.  Conditional on the two open frontier clauses,
no additional hypothesis and no placeholder is used. -/
theorem abcConjecture_of_frontierHeightRegionEstimates {X : Type u}
    (W : IQHullLogVolumeInterface X) (x : Nat → Nat → Nat → X)
    (hheight : FrontierHeightComparisonClause W (fun _ _ => x))
    (hmain : FrontierRegionComparisonClause W (fun _ _ => x)) :
    ABCConjecture :=
  abcConjecture_of_literalLogVolumeEstimates
    (frontierRegionLogVolume W x) (frontierHullVolume W)
    (abcHeightEstimate_of_frontierHeightComparison W x hheight)
    (abcMainEstimate_of_frontierRegionComparison W x hmain)

/-- The corresponding ABC-form additive height bound, from the same two clauses. -/
theorem abcFormAdditiveHeightBound_of_frontierHeightRegionEstimates {X : Type u}
    (W : IQHullLogVolumeInterface X) (x : Nat → Nat → Nat → X)
    (hheight : FrontierHeightComparisonClause W (fun _ _ => x))
    (hmain : FrontierRegionComparisonClause W (fun _ _ => x)) :
    ABCFormAdditiveHeightBound :=
  additiveHeightBound_of_literalLogVolumeEstimates
    (frontierRegionLogVolume W x) (frontierHullVolume W)
    (abcHeightEstimate_of_frontierHeightComparison W x hheight)
    (abcMainEstimate_of_frontierRegionComparison W x hmain)

def abcEstimateRows : List (String × String × String) :=
  [ ("FrontierHeightComparisonClause", "ABCBridge frontier F4 (open IUT IV section 2)", "EXPLICIT DONOR CLAUSE (open)"),
    ("FrontierRegionComparisonClause", "ABCBridge frontier F5 (open IUT IV section 2)", "EXPLICIT DONOR CLAUSE (open)"),
    ("frontierRegionLogVolume", "region log-volume readout from W and fixed point datum", "DEFINED"),
    ("abcHeightEstimate_of_frontierHeightComparison", "F4 => hheight shape", "PROVED (from F4)"),
    ("abcMainEstimate_of_frontierRegionComparison", "F5 => hmain shape", "PROVED (from F5)"),
    ("abcConjecture_of_frontierHeightRegionEstimates", "F4 + F5 => ABCConjecture via Stage-5", "PROVED (conditional on F4,F5)") ]

theorem abcEstimateRows_length : abcEstimateRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCMainEstimateActual

end