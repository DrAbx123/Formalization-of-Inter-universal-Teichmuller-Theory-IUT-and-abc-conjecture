/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchCAbcActual
import Mathlib.Tactic

/-! # P7/NORM-ARCH-C: degree-one arch factors (single declaration cluster) -/

/-
| field | value |
|---|---|
| Status | green attempt: `1/[K:Q] = 1` and `1/(2[K:Q]) = 1/2` for degree-one K (ℚ instance included) |
| GAP | no explicit K/[K:Q] instance in the ABC route (GAP-NORM-ARCH-C-K) |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ArchFactorDegreeOneActual

/-- Degree-one arch factor is 1. -/
theorem archFactor_eq_one_of_finrank_one
    {K : Type*} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) :
    (1 : ℝ) / (Module.finrank ℚ K : ℝ) = 1 := by
  rw [h]
  norm_num

/-- Degree-one toric arch factor is 1/2. -/
theorem toricArchFactor_eq_half_of_finrank_one
    {K : Type*} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) :
    (1 : ℝ) / ((2 : ℝ) * (Module.finrank ℚ K : ℝ)) = 1 / 2 := by
  rw [h]
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1ArchFactorDegreeOneActual