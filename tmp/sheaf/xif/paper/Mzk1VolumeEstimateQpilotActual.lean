/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # Mzk1VolumeEstimateQpilotActual — VolumeEstimate substantive advance (A611)

Volume-side consequences of the bridge comparison data: the comparison-region
log-volume bound, its finiteness on ABC triples, the `ENNReal.ofReal`/`toReal`
faithfulness, and monotonicity of the estimate in `ε` (with nonnegative weight).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1VolumeEstimateQpilotActual

open LeanFormal.IUT
open MeasureTheory
open scoped ENNReal

universe u

/-- Volume estimate: the explicit `∃ D` bound for the comparison-region volume. -/
theorem volume_estimate_exists {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (C.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D := by
  exact C.regionVolume_le_normalizedWeight

/-- The comparison-region volume is finite on ABC triples. -/
theorem volume_estimate_finite {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (C.comparisonRegion a b c) < ⊤ := by
  exact C.comparisonRegion_logVolume_lt_top

/-- The `ENNReal.ofReal` round-trip of the comparison-region volume. -/
theorem volume_estimate_ofReal {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    {a b c : Nat} (habc : IsABCTriple a b c) :
    ENNReal.ofReal (W.logVolume (C.comparisonRegion a b c)).toReal =
      W.logVolume (C.comparisonRegion a b c) := by
  exact cor312ComparisonRegionVolume_ofReal_toReal C habc

/-- Monotonicity of the volume estimate in `ε` (real arithmetic): if `0 ≤ weight`
and `ε₁ ≤ ε₂`, the estimate with `ε₁` is dominated by the `ε₂` estimate with the
same `D` up to the explicit `(ε₂ - ε₁)·weight` slack. -/
theorem volume_estimate_mono_eps {w theta D eps1 eps2 : Real}
    (hw : 0 ≤ w) (h : eps1 ≤ eps2)
    (hbound : 0 ≤ (1 + eps2) * w + theta + D) :
    (1 + eps1) * w + theta + D ≤ (1 + eps2) * w + theta + D := by
  nlinarith

#check volume_estimate_exists
#check volume_estimate_finite
#check volume_estimate_ofReal
#check volume_estimate_mono_eps

end LeanFormal.IUT.XiFPaper.Mzk1VolumeEstimateQpilotActual
end
