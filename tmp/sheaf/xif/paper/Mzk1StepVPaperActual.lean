import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1StepVPaperActual — StepV node: paper-form final inequality (exact restatement)

DAG node: IUTIV StepV (tree asset).  The core real-number estimates are proved in
LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean; this file exposes the exact
paper-form final inequality with l = 2n+1 >= 5, matching the Step (v) display shape
(IV L1757-L1783).  No new analytic input; a restatement/consumer lemma for the fragment.

No closure claim; gate NOT PASSED. Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVPaperActual

open LeanFormal.IUT.IUTIV.StepVProcessionAverage

/-- Paper-form Step (v) inequality: for l = 2n+1 >= 5 and D,S,T >= 0,
the procession-normalized bound is at most the right-hand-side display. -/
theorem stepV_paperForm_le (n : ℕ) (hn : 2 ≤ n) (D Q S T : ℝ)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    ((2 * (n : ℝ) + 1) + 5) / 4 * D - ((2 * (n : ℝ) + 1) + 1) / 24 * Q + S +
        ((2 * (n : ℝ) + 1) + 5) * T ≤
      ((2 * (n : ℝ) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : ℝ) + 1)) * D - Q / 6 +
          4 / (2 * (n : ℝ) + 1) * S + 20 / 3 * T) := by
  have h := processionAverage_le n hn D Q S T hD hS hT
  rwa [processionAverage_eq n (by omega)] at h

/-- The same inequality with l = 2n+1 >= 5 explicitly. -/
theorem stepV_paperForm_le_l (n : ℕ) (hn : 2 ≤ n) (D Q S T : ℝ)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    let l : ℝ := 2 * (n : ℝ) + 1
    (l + 5) / 4 * D - (l + 1) / 24 * Q + S + (l + 5) * T ≤
      (l + 1) / 4 * ((1 + 4 / l) * D - Q / 6 + 4 / l * S + 20 / 3 * T) := by
  intro l
  simpa [l] using stepV_paperForm_le n hn D Q S T hD hS hT

/-- Rows: StepV node consumer status. -/
def stepVPaperRows : List (String × String × String) :=
  [ ("StepV real-number algebra", "processionAverage_eq / processionAverage_le (core)", "PROVED (reuse)"),
    ("paper-form final inequality", "stepV_paperForm_le / stepV_paperForm_le_l", "PROVED (restatement)"),
    ("scope", "real-number layer only; arithmetic inputs free; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem stepVPaperRows_length : stepVPaperRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepVPaperActual

end
