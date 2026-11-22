/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#7: reusable bound-transfer arithmetic -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1HullBoundTransferLibActual

/-- `V <= A + C0` and `C0 <= C1` imply `V <= A + C1`. -/
theorem transfer_add {V A C0 C1 : ℝ}
    (h : V ≤ A + C0) (hC : C0 ≤ C1) : V ≤ A + C1 := by linarith

/-- `V <= A + C0` and `A + C0 <= B` imply `V <= B`. -/
theorem transfer_total {V A C0 B : ℝ}
    (h : V ≤ A + C0) (hB : A + C0 ≤ B) : V ≤ B := by linarith

/-- If `V <= A` and `A <= B`, then `V <= B`. -/
theorem transfer_le {V A B : ℝ} (h : V ≤ A) (hAB : A ≤ B) : V ≤ B := by linarith

end LeanFormal.IUT.XiFPaper.Mzk1HullBoundTransferLibActual