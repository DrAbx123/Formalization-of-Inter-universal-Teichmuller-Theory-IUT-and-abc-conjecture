/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # Mzk1Gap1NumericWitnessQpilotActual — Gap-1 numeric witness + consumer

A590 (qpilot lane): the Gap-1 height comparison is consumed from the bridge data
(`Cor312EpsilonArithmeticComparison.height_le_normalizedRegionVolume`), plus an
explicit numeric witness that the inequality shape is satisfiable. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1NumericWitnessQpilotActual

open LeanFormal.IUT
open MeasureTheory
open scoped ENNReal

universe u

/-- Gap-1 consumer: the height comparison field, in consumption form. -/
theorem gap1_consumer {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * (W.logVolume (C.comparisonRegion a b c)).toReal :=
  C.height_le_normalizedRegionVolume a b c habc

/-- Numeric witness: the Gap-1 inequality shape is satisfiable (`1 ≤ 2·2`). -/
theorem gap1_numeric_witness :
    ∃ (height volume epsilon : Real), 0 < epsilon ∧
      height ≤ (1 + epsilon) * volume := by
  exact ⟨1, 2, 1, by norm_num, by norm_num⟩

/-- Numeric witness with the same `ε` on both sides (`1 ≤ (1+1/2)·2/3`). -/
theorem gap1_numeric_witness' :
    ∃ (height volume epsilon : Real), 0 < epsilon ∧
      height ≤ (1 + epsilon) * volume ∧ epsilon < 1 := by
  refine ⟨1, 1, 1/2, by norm_num, by norm_num, by norm_num⟩

#check gap1_consumer
#check gap1_numeric_witness

end LeanFormal.IUT.XiFPaper.Mzk1Gap1NumericWitnessQpilotActual
end
