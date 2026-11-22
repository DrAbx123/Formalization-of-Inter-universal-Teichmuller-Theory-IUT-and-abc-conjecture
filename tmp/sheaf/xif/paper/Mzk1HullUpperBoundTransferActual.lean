/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullUpperBoundInterfaceActual
import Mathlib.Tactic

/-! # P7/#7: transfer arithmetic for the hull upper-bound interface -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1HullUpperBoundTransferActual

open LeanFormal.IUT.XiFPaper.Mzk1HullUpperBoundInterfaceActual

/-- If the bound holds with `C0` and `C0 <= C1`, it holds with `C1`. -/
theorem hullUpperBound_mono_C0 {V l d f C0 C1 : ℝ}
    (h : HullUpperBound V l d f C0) (hC : C0 ≤ C1) :
    HullUpperBound V l d f C1 := by
  unfold HullUpperBound at *
  linarith

/-- Transitivity of the bound: if the main term plus `C0` is at most `C1`, then `V <= C1`. -/
theorem hullUpperBound_le_of_main_add {V l d f C0 C1 : ℝ}
    (h : HullUpperBound V l d f C0)
    (hC : (1 / 4) * l * (Real.log d + Real.log f) + C0 ≤ C1) :
    V ≤ C1 := by
  unfold HullUpperBound at h
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1HullUpperBoundTransferActual