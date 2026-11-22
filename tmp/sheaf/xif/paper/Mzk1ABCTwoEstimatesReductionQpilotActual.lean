/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCEntryQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEntryGap2QpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import Mathlib.Tactic

/-! # Mzk1ABCTwoEstimatesReductionQpilotActual — two-estimates reduction interface

A596 (qpilot lane): integration interface for the two ABC estimates: thin
re-exports of the conditional height bound, the Gap-2 named estimate consumer,
the arithmetic chaining/absorption, and a numeric witness. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

/-- Thin re-export: conditional height bound from the bridge interface. -/
theorem reduction_heightBound (D : Cor312ToABCBridgeInterface) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  abcEntry_heightBound D

/-- Thin re-export: Gap-2 named region-volume bound. -/
theorem reduction_gap2 {X : Type} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (C.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D :=
  gap2_regionVolume_bound C

/-- Thin re-export: the two estimates chain into the absorbed bound. -/
theorem reduction_chain {h v w t D eps : Real}
    (h0 : 0 ≤ eps) (h1 : eps ≤ 1) (hw : 0 ≤ w)
    (hge1 : h ≤ (1 + eps) * v)
    (hge2 : v ≤ (1 + eps) * w + t + D) :
    h ≤ (1 + 3 * eps) * w + (1 + eps) * (t + D) :=
  height_le_absorbed h0 h1 hw (height_le_of_twoEstimates h0 hge1 hge2)

/-- The two-estimates reduction interface. -/
structure TwoEstimatesReduction where
  heightBound : Cor312ToABCBridgeInterface.{0} →
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A
  chain : ∀ {h v w t D eps : Real}, 0 ≤ eps → eps ≤ 1 → 0 ≤ w →
    h ≤ (1 + eps) * v → v ≤ (1 + eps) * w + t + D →
    h ≤ (1 + 3 * eps) * w + (1 + eps) * (t + D)
  numericWitness : ∃ (h v w t D eps : Real), 0 < eps ∧ eps ≤ 1 ∧ 0 ≤ w ∧
    h ≤ (1 + eps) * v ∧ v ≤ (1 + eps) * w + t + D

/-- The constructed reduction interface. -/
noncomputable def twoEstimatesReduction : TwoEstimatesReduction where
  heightBound := fun D => reduction_heightBound D
  chain := fun {h v w t D eps} h0 h1 hw hge1 hge2 =>
    reduction_chain h0 h1 hw hge1 hge2
  numericWitness := by
    refine ⟨1, 2, 2, 0, 0, 1/2, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num⟩

#check twoEstimatesReduction

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionQpilotActual
end
