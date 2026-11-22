import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4ScalingDirectionStudyActual (stage4 lane; scaling-direction study)

A654 module: research on the SCALING DIRECTION of the paper comparison region.
Two model candidates are compared in the real line model `X = ℝ`, unit region [0,1]:
* FORWARD scaling `x ↦ x·(N+1)` (growing regions; the canonical direction): model
  volumes grow with the triple, and the model Gap-1 comparison HOLDS;
* INVERSE scaling `x ↦ x/(N+1)` (shrinking regions): the model Gap-1 comparison FAILS
  for large triples, because heights grow while the volume shrinks.
This is evidence (model-level, no paper conclusion changed) that the forward direction
is the correction candidate.  `Mzk1PaperComparisonRegionScalingActual` (mainline) is
only READ.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ScalingDirectionStudyActual

open MeasureTheory
open scoped ENNReal

/-- Model height of a triple with total `N = a+b+c`. -/
def modelHeight (a b c : Nat) : Real := ((a + b + c : Nat) : Real)

/-- FORWARD scaling model region: `[0, N+1]`. -/
def forwardRegion (a b c : Nat) : Set Real :=
  Set.Icc 0 (((a + b + c : Nat) : Real) + 1)

/-- INVERSE scaling model region: `[0, 1/(N+1)]`. -/
def inverseRegion (a b c : Nat) : Set Real :=
  Set.Icc 0 (1 / (((a + b + c : Nat) : Real) + 1))

/-- Forward model Gap 1 HOLDS for every `ε > 0`. -/
theorem forward_scaling_gap1 :
    ∀ ε : Real, 0 < ε → ∀ a b c : Nat,
      modelHeight a b c <=
        (1 + ε) * (volume (forwardRegion a b c)).toReal := by
  intro ε hε a b c
  have hvol : (volume (forwardRegion a b c)).toReal =
      ((a + b + c : Nat) : Real) + 1 := by
    unfold forwardRegion
    rw [Real.volume_Icc]
    have h0 : (0 : Real) ≤ ((a + b + c : Nat) : Real) + 1 := by positivity
    rw [show ((((a + b + c : Nat) : Real) + 1) - 0) =
      ((a + b + c : Nat) : Real) + 1 by ring]
    rw [ENNReal.toReal_ofReal h0]
  rw [hvol]
  unfold modelHeight
  nlinarith

/-- INVERSE model Gap 1 FAILS: at `ε = 1`, the triple `(2,0,0)` violates it. -/
theorem inverse_scaling_gap1_fails :
    ¬ (∀ a b c : Nat,
        modelHeight a b c ≤ (1 + 1) * (volume (inverseRegion a b c)).toReal) := by
  intro h
  have h2 := h 2 0 0
  simp only [modelHeight, inverseRegion] at h2
  rw [Real.volume_Icc] at h2
  have h0 : (0 : Real) ≤ 1 / (((2 + 0 + 0 : Nat) : Real) + 1) := by positivity
  rw [show (1 : Real) / (((2 + 0 + 0 : Nat) : Real) + 1) - 0 =
      1 / (((2 + 0 + 0 : Nat) : Real) + 1) by ring] at h2
  rw [ENNReal.toReal_ofReal h0] at h2
  norm_num at h2

/-- The correction candidate: the FORWARD (growing) scaling is the only model direction
under which the Gap-1 comparison can hold uniformly. -/
theorem forward_is_correction_candidate :
    (∀ ε : Real, 0 < ε → ∀ a b c : Nat,
      modelHeight a b c ≤ (1 + ε) * (volume (forwardRegion a b c)).toReal) ∧
      ¬ (∀ a b c : Nat,
        modelHeight a b c ≤ (1 + 1) * (volume (inverseRegion a b c)).toReal) :=
  ⟨forward_scaling_gap1, inverse_scaling_gap1_fails⟩

#check modelHeight
#check forwardRegion
#check inverseRegion
#check forward_scaling_gap1
#check inverse_scaling_gap1_fails
#check forward_is_correction_candidate

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ScalingDirectionStudyActual
end
