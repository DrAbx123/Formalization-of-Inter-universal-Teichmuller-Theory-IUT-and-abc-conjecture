import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: label-averaged procession log-volume (vendor-adapted)

Adapted from vendor promachina Iut/Stage1/IUTStage1SourceCore.lean:1137
structure IUTStage1LabelAveragedProcessionLogVolume and :1154
IUTStage1WeightedLabelAveragedProcessionLogVolume.  Re-proved generically with
Mathlib Finset sums: a label family of real log-volume values with its average
(and weighted average), characterized by the multiplication law instead of a
division.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorLabelAveragedLogVolumeActual

universe u

/-- A label-averaged log-volume datum: values on a finite label family plus
their average, characterized by average * n = sum of the values. -/
structure SourceLabelAveragedLogVolume (n : ℕ) where
  /-- the per-label log-volume values -/
  values : Fin n → ℝ
  /-- the label average -/
  average : ℝ
  /-- the average law: average * n = sum of the values -/
  average_law : average * (n : ℝ) = ∑ i, values i

/-- Every label family of real values has a label-averaged log-volume (n > 0). -/
def sourceLabelAveragedLogVolumeOf (n : ℕ) (hn : 0 < n) (values : Fin n → ℝ) :
    SourceLabelAveragedLogVolume n where
  values := values
  average := (∑ i, values i) / (n : ℝ)
  average_law := by
    rw [div_mul_cancel₀]
    exact Nat.cast_ne_zero.mpr hn.ne'

/-- A weighted label-averaged log-volume datum: weights on the label family and
the weighted average, characterized by weightedAverage * totalWeight = weighted
sum. -/
structure SourceWeightedLabelAveragedLogVolume (n : ℕ) where
  /-- the per-label log-volume values -/
  values : Fin n → ℝ
  /-- the per-label weights -/
  weights : Fin n → ℝ
  /-- the weighted average -/
  weightedAverage : ℝ
  /-- the weighted-average law -/
  weightedAverage_law :
    weightedAverage * (∑ i, weights i) = ∑ i, weights i * values i

/-- Every label family with nonzero total weight has a weighted label-averaged
log-volume. -/
def sourceWeightedLabelAveragedLogVolumeOf (n : ℕ) (values weights : Fin n → ℝ)
    (hW : (∑ i, weights i) ≠ 0) :
    SourceWeightedLabelAveragedLogVolume n where
  values := values
  weights := weights
  weightedAverage := (∑ i, weights i * values i) / (∑ i, weights i)
  weightedAverage_law := by
    rw [div_mul_cancel₀]
    exact hW

end LeanFormal.IUT.XiFPaper.S3139VendorLabelAveragedLogVolumeActual
