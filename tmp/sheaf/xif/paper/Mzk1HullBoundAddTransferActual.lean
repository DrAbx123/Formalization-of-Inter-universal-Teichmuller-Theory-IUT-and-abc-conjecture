/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#7: additive transfer arithmetic for the hull bound -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1HullBoundAddTransferActual

/-- Main term. -/
noncomputable def mainTerm (l d f : ℝ) : ℝ := (1 / 4) * l * (Real.log d + Real.log f)

/-- If `V <= main + C0` and `C0 <= C1`, then `V <= main + C1`. -/
theorem transfer_C0 {V l d f C0 C1 : ℝ}
    (h : V ≤ mainTerm l d f + C0) (hC : C0 ≤ C1) :
    V ≤ mainTerm l d f + C1 := by
  unfold mainTerm at *
  linarith

/-- If `V <= main + C0` and `main + C0 <= C1`, then `V <= C1`. -/
theorem transfer_total {V l d f C0 C1 : ℝ}
    (h : V ≤ mainTerm l d f + C0) (hC : mainTerm l d f + C0 ≤ C1) :
    V ≤ C1 := by
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1HullBoundAddTransferActual