/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Mzk1RegionNecessitySummaryQpilotActual
import Mathlib.Tactic

/-! # Mzk1ScalingDirectionResearchQpilotActual — scaling direction research (A654)

Structural research on the triple-dependent scaling direction of the paper
comparison region `s '' (unitRegion ∪ {pt})`:
* only the values of the scaling on the source region matter (congruence);
* the constant-region specialization of Gap 1 is false for every scaling direction
  (via the green obstruction `no_constantRegion_heightComparison`).
No conclusion is changed; this is research evidence for the correction candidates. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionResearchQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

/-- The scaled comparison region with an arbitrary scaling direction `s`. -/
def scaledRegion {X : Type u} (s : X → X) (A : Set X) : Set X := s '' A

/-- Scaling directions that agree on the source region give the same region. -/
theorem scaledRegion_congr {X : Type u} {s1 s2 : X → X} {A : Set X}
    (h : ∀ x ∈ A, s1 x = s2 x) :
    scaledRegion s1 A = scaledRegion s2 A :=
  Set.image_congr h

/-- The scaling direction is irrelevant off the source region: if two scalings
agree on `A` they define identical comparison regions. -/
theorem scaling_direction_irrelevant_off_region {X : Type u} {s1 s2 : X → X}
    {A : Set X} (h : ∀ x ∈ A, s1 x = s2 x) :
    s1 '' A = s2 '' A :=
  Set.image_congr h

/-- **Gap-1 test**: the constant-region specialization fails for every scaling
direction: `no_constantRegion_heightComparison` applies to `s '' A` as a fixed region. -/
theorem gap1_test_constantRegion_fails {X : Type u} (W : IQHullLogVolumeInterface X)
    (R : Set X) (epsilon : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (W.logVolume R).toReal) :=
  regionNecessity_noConstant W R epsilon

/-- Research rows for the scaling direction. -/
def scalingDirectionRows : List (String × String) :=
  [ ("scaling agrees on source region => same region", "PROVED"),
    ("scaling direction irrelevant off region", "PROVED"),
    ("constant-region Gap 1 fails", "PROVED (obstruction)"),
    ("triple-dependent scale candidate", "RESEARCH (mainline tripleScale)") ]

theorem scalingDirectionRows_length : scalingDirectionRows.length = 4 := rfl

#check scaledRegion_congr
#check gap1_test_constantRegion_fails
#check scalingDirectionRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionResearchQpilotActual
end
