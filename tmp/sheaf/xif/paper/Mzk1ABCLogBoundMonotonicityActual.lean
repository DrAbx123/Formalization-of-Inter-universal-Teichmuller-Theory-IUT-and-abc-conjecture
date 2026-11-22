import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ABCLogBoundMonotonicityActual — ABC log-bound monotonicity consumers

DAG node: iutiv-abc:G0.log.  Proves the two basic monotonicity facts for the
fixed-constant log bound ABCLogBound ε A: increasing the additive constant, and
increasing ε >= 0, preserve the bound.  These are the elementary calibration
lemmas needed when transporting ABCConjecture across equivalent formulations.
No new arithmetic input; no closure; gate NOT PASSED.  Registry 14041; no edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCLogBoundMonotonicityActual

open LeanFormal.IUT

/-- Increasing the additive constant preserves ABCLogBound. -/
theorem ABCLogBound_mono_A {epsilon A B : Real} (hAB : A ≤ B)
    (h : ABCLogBound epsilon A) : ABCLogBound epsilon B := by
  intro a b c habc
  have h1 := h a b c habc
  linarith

/-- Increasing epsilon >= 0 preserves ABCLogBound (radical log is nonnegative). -/
theorem ABCLogBound_mono_epsilon {epsilon₁ epsilon₂ A : Real} (heps : epsilon₁ ≤ epsilon₂)
    (h : ABCLogBound epsilon₁ A) : ABCLogBound epsilon₂ A := by
  intro a b c habc
  have h1 := h a b c habc
  have hlog : 0 ≤ Real.log (radical (a * b * c) : Real) := by
    apply Real.log_nonneg
    have hr : 0 < radical (a * b * c) := radical_pos _
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hr) : 1 ≤ radical (a * b * c))
  have hcoef : (1 + epsilon₁) ≤ (1 + epsilon₂) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hlog
  linarith

/-- The log conjecture in the fixed-bound form. -/
theorem abcLogConjecture_iff_forall_bound :
    ABCLogConjecture ↔ ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ABCLogBound epsilon A :=
  Iff.rfl

/-- Rows: log-bound consumer status. -/
def abcLogBoundMonoRows : List (String × String × String) :=
  [ ("monotone in A", "ABCLogBound_mono_A", "PROVED"),
    ("monotone in epsilon", "ABCLogBound_mono_epsilon", "PROVED (radical log nonneg)"),
    ("conjecture unfolding", "abcLogConjecture_iff_forall_bound", "DEF/iff"),
    ("scope", "elementary calibration; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem abcLogBoundMonoRows_length : abcLogBoundMonoRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCLogBoundMonotonicityActual

end
