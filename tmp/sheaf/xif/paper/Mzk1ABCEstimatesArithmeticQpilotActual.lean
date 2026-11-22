/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1ABCEstimatesArithmeticQpilotActual — arithmetic lemmas for the two ABC estimates

A594 (qpilot lane): real-valued intermediate lemmas composing the two named
estimates (Gap 1 height comparison and Gap 2 region log-volume comparison).
These do NOT change the bridge objects; they are the pure-arithmetic steps used
to chain the two estimates into the height-weight bound. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual

/-- Gap 1 composed with Gap 2: `h ≤ (1+ε)·v` and `v ≤ (1+ε)·w + t + D` give
`h ≤ (1+ε)·((1+ε)·w + t + D)` (two `(1+ε)` losses retained). -/
theorem height_le_of_twoEstimates {h v w t D eps : Real}
    (heps : 0 ≤ eps)
    (h1 : h ≤ (1 + eps) * v)
    (h2 : v ≤ (1 + eps) * w + t + D) :
    h ≤ (1 + eps) * ((1 + eps) * w + t + D) := by
  have h1e : (0 : Real) ≤ 1 + eps := by linarith
  have hmul : (1 + eps) * v ≤ (1 + eps) * ((1 + eps) * w + t + D) :=
    mul_le_mul_of_nonneg_left h2 h1e
  linarith

/-- Absorption step: for `0 ≤ ε ≤ 1`, `(1+ε)^2 ≤ 1 + 3ε`. -/
theorem one_add_sq_le_one_add_three {eps : Real} (h0 : 0 ≤ eps) (h1 : eps ≤ 1) :
    (1 + eps) * (1 + eps) ≤ 1 + 3 * eps := by
  nlinarith

/-- Absorbed chained comparison: with `0 ≤ ε ≤ 1` and `0 ≤ w`, the two `(1+ε)`
losses are re-absorbed into `(1+3ε)w + (1+ε)(t+D)`. -/
theorem height_le_absorbed {h w t D eps : Real} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (hw : 0 ≤ w)
    (hchain : h ≤ (1 + eps) * ((1 + eps) * w + t + D)) :
    h ≤ (1 + 3 * eps) * w + (1 + eps) * (t + D) := by
  have hsq : (1 + eps) * (1 + eps) ≤ 1 + 3 * eps :=
    one_add_sq_le_one_add_three h0 h1
  have hstep : (1 + eps) * ((1 + eps) * w) ≤ (1 + 3 * eps) * w := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hsq hw
  have hexp : (1 + eps) * ((1 + eps) * w + t + D) =
      (1 + eps) * ((1 + eps) * w) + (1 + eps) * (t + D) := by ring
  calc h ≤ (1 + eps) * ((1 + eps) * w + t + D) := hchain
    _ = (1 + eps) * ((1 + eps) * w) + (1 + eps) * (t + D) := hexp
    _ ≤ (1 + 3 * eps) * w + (1 + eps) * (t + D) :=
        add_le_add hstep (le_rfl)

#check height_le_of_twoEstimates
#check height_le_absorbed

end LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
end
