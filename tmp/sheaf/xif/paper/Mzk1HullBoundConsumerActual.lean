/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullUpperBoundInterfaceActual
import Mathlib.Tactic

/-! # P7/#7: consumer of the named hull upper-bound interface -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1HullBoundConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1HullUpperBoundInterfaceActual

/-- Unfolded consumer: `HullUpperBound V l d f C0` gives the explicit inequality. -/
theorem hullBound_apply {V l d f C0 : ℝ}
    (h : HullUpperBound V l d f C0) :
    V ≤ (1 / 4) * l * (Real.log d + Real.log f) + C0 := h

/-- If additionally the main term plus `C0` is nonpositive, then `V ≤ 0`. -/
theorem hullBound_nonpos_of_main_add_nonpos {V l d f C0 : ℝ}
    (h : HullUpperBound V l d f C0)
    (hmain : (1 / 4) * l * (Real.log d + Real.log f) + C0 ≤ 0) : V ≤ 0 := by
  unfold HullUpperBound at h
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1HullBoundConsumerActual