/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
/-! # Torsion-ratio log donor -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
/-- If `T ≤ q1 * C`, then `log(q1/T) ≥ -log C`. -/
theorem log_torsion_ratio_ge_neg_log
    {q1 T C : Nat} (hq1 : 0 < q1) (hC : 0 < C) (hTpos : 0 < T)
    (hT : T ≤ q1 * C) :
    - Real.log (C : ℝ) ≤ Real.log ((q1 : ℝ) / (T : ℝ)) := by
  have hTposR : 0 < (T : ℝ) := by exact_mod_cast hTpos
  have hq1R : 0 < (q1 : ℝ) := by exact_mod_cast hq1
  have hCR : 0 < (C : ℝ) := by exact_mod_cast hC
  have hle : (T : ℝ) ≤ (q1 : ℝ) * (C : ℝ) := by exact_mod_cast hT
  have hlog := Real.log_le_log hTposR hle
  rw [Real.log_mul hq1R.ne' hCR.ne'] at hlog
  rw [Real.log_div hq1R.ne' hTposR.ne']
  linarith
end LeanFormal.IUT.LocalFieldLogarithm
end