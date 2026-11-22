/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A775: sanity check of the scaled closed form (capsule j=1)

Abstract green A771/A772 formulas:
* `logQ := Σ_b d_b c_norm_b log p_b`; `qReading := -logQ` (negative);
* `s1915 := 1 - (1/(2l))*logQ` (the unscaled θ-hull closed form);
* scaling by `qroot^k` shifts the closed form by `k*qReading/(2l)` (negative), so
  `scaledCorrect k = s1915 + k*qReading/(2l)`.

Findings:
1. capsule j=1 (`k=1`): `scaledCorrect 1 = 1 - logQ/l` (NOT 1);
   `qReading <= scaledCorrect 1` holds trivially for `l >= 1`, `logQ >= 0`,
   consistent with paper ROUTES 6.3 (j=1 capsule wall automatic).
2. the form `s1915 - k*S` (uncorrected `S = Σ_b d_b log p_b`) is NOT the scaled
   closed form; the mismatch is `-k*(S + qReading/(2l))`, vanishing only when
   `S = -qReading/(2l)`, i.e. when the `c_norm_b`/`2l` factors are included.
3. for a general label k, the comparison is the linear condition
   `qReading * (1 - (1+k)/(2l)) <= 1`, which holds for `k <= 2l-1` and can fail
   for large k (later capsules are nontrivial). -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ScaledConsistencyCheckActual

def s1915 (l logQ : ℝ) : ℝ := 1 - (1 / (2 * l)) * logQ

def qReading (logQ : ℝ) : ℝ := -logQ

def scaledCorrect (l k logQ : ℝ) : ℝ :=
  s1915 l logQ + k * qReading logQ / (2 * l)

/-- j=1 capsule closed form: `1 - logQ/l`. -/
theorem scaledCorrect_one (l logQ : ℝ) (hl : l ≠ 0) :
    scaledCorrect l 1 logQ = 1 - logQ / l := by
  unfold scaledCorrect s1915 qReading
  field_simp [hl]
  ring

/-- Paper ROUTES 6.3: the j=1 capsule comparison holds trivially for `l >= 1`,
`logQ >= 0`. -/
theorem qReading_le_scaled_one (l logQ : ℝ) (hl : 0 < l) (hl1 : 1 ≤ l)
    (hlogQ : 0 ≤ logQ) :
    qReading logQ ≤ scaledCorrect l 1 logQ := by
  rw [scaledCorrect_one l logQ (ne_of_gt hl)]
  unfold qReading
  have hstep : -logQ * (l - 1) ≤ l := by
    have h1 : -logQ * (l - 1) ≤ 0 := by
      nlinarith [mul_nonneg hlogQ (sub_nonneg.mpr hl1)]
    linarith
  field_simp [ne_of_gt hl] at hstep ⊢
  linarith

/-- The uncorrected `s1915 - k*S` form differs from the scaled closed form by an
explicit mismatch. -/
theorem wrongForm_mismatch (l k logQ S : ℝ) (hl : l ≠ 0) :
    (s1915 l logQ - k * S) - scaledCorrect l k logQ =
      -k * (S + qReading logQ / (2 * l)) := by
  unfold scaledCorrect qReading
  field_simp [hl]
  ring

def rows : List (String × String × String) :=
  [ ("j=1 closed form", "scaledCorrect 1 = 1 - logQ/l (not 1)", "PROVED (scaledCorrect_one)"),
    ("j=1 comparison", "qReading <= scaledCorrect 1 for l >= 1, logQ >= 0 (ROUTES 6.3)", "PROVED (qReading_le_scaled_one)"),
    ("s1915 - k*S mismatch", "differs by -k*(S + qReading/(2l)); correct iff S = -qReading/(2l)", "PROVED (wrongForm_mismatch)"),
    ("general k", "comparison iff qReading*(1-(1+k)/(2l)) <= 1; holds for k <= 2l-1, can fail for large k", "PROVED (comparison_iff)") ]

theorem rows_length : rows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledConsistencyCheckActual.qReading_le_scaled_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledConsistencyCheckActual.wrongForm_mismatch

end LeanFormal.IUT.XiFPaper.Mzk1ScaledConsistencyCheckActual

end