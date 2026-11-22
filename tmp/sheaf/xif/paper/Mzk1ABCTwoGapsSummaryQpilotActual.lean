/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap1NumericWitnessQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEntryGap2QpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual

/-! # Mzk1ABCTwoGapsSummaryQpilotActual — ABC two-gap summary (A590)

One summary object for the two Cor 3.12 -> ABC estimate gaps:
* Gap 1 (height comparison) and Gap 2 (region log-volume estimate),
each exposed as a named statement taken from the bridge data, together with
their numeric non-vacuity witnesses. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoGapsSummaryQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.Mzk1Gap1NumericWitnessQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual
open MeasureTheory
open scoped ENNReal

universe u

/-- Gap-1 statement shape on a hull interface and `ε`. -/
def Gap1Statement {X : Type u} (W : IQHullLogVolumeInterface X)
    (C : ∀ ε : Real, Cor312EpsilonArithmeticComparison W ε) : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * (W.logVolume ((C epsilon).comparisonRegion a b c)).toReal

/-- Gap-2 statement shape on a hull interface and `ε`. -/
def Gap2Statement {X : Type u} (W : IQHullLogVolumeInterface X)
    (C : ∀ ε : Real, Cor312EpsilonArithmeticComparison W ε) : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume ((C epsilon).comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D

/-- The two gap statements hold from the bridge comparison data. -/
theorem twoGaps_of_comparison {X : Type u} (W : IQHullLogVolumeInterface X)
    (C : ∀ ε : Real, Cor312EpsilonArithmeticComparison W ε) :
    Gap1Statement W C ∧ Gap2Statement W C := by
  constructor
  · intro epsilon hepsilon a b c habc
    exact (C epsilon).height_le_normalizedRegionVolume a b c habc
  · intro epsilon hepsilon
    exact (C epsilon).regionVolume_le_normalizedWeight

/-- Numeric witnesses for both gap shapes (non-vacuity). -/
theorem twoGaps_numeric_witness :
    (∃ (height volume epsilon : Real), 0 < epsilon ∧
        height ≤ (1 + epsilon) * volume) ∧
      (∃ (regionVolume : ENNReal) (eps weight theta D : Real),
        0 ≤ (1 + eps) * weight + theta + D ∧
          LeanFormal.IUT.Objects.ABCBridgeGap2.SNamed regionVolume eps weight theta D) :=
  ⟨gap1_numeric_witness, ⟨0, 0, 0, 0, 0, by norm_num,
    by unfold LeanFormal.IUT.Objects.ABCBridgeGap2.SNamed; simp⟩⟩

#check twoGaps_of_comparison
#check twoGaps_numeric_witness

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoGapsSummaryQpilotActual
end
