import Mathlib

/-! # TOOL (generic): weighted readout comparison for regional log-volume sums

Lead policy: when a proof is blocked by a missing lemma, manufacture a general
reusable tool.  This file provides the generic weighted-sum comparison tools used
by the S3131 regional readout comparisons (pointwise comparison => weighted
regional comparison; strict positivity of the region gap => strict magnitude
inequality), with zero residual data: consumers instantiate w, y, z. -/

namespace LeanFormal.IUT.XiFPaper.S3131WeightedReadoutTool

open scoped BigOperators

/-- Generic weighted regional comparison: pointwise comparison implies weighted
regional comparison for nonnegative weights. -/
theorem weighted_sum_le_of_pointwise {ι : Type*} [Fintype ι]
    (w y z : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (h : ∀ i, y i ≤ z i) :
    (∑ i, w i * y i) ≤ ∑ i, w i * z i := by
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_left (h i) (hw i)

/-- Generic weighted magnitude bound: nonpositive readouts with |y| ≤ |z| give
the weighted magnitude inequality. -/
theorem weighted_sum_neg_le_of_pointwise {ι : Type*} [Fintype ι]
    (w y z : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (h : ∀ i, y i ≤ z i) :
    -∑ i, w i * z i ≤ -∑ i, w i * y i := by
  have hsum := weighted_sum_le_of_pointwise w y z hw h
  linarith

/-- Generic normalized-weight identity: total-one weights preserve constant readouts. -/
theorem weighted_sum_const_of_sum_one {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ℝ) (hw : ∑ i, w i = 1) :
    (∑ i, w i * c) = c := by
  rw [← Finset.sum_mul, hw, one_mul]

end LeanFormal.IUT.XiFPaper.S3131WeightedReadoutTool
