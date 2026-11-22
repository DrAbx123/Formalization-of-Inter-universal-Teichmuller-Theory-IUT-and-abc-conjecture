/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#7: C0 nonnegativity interface for the hull upper bound -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C0NonnegInterfaceActual

/-- Named condition: the hull-bound constant `C0` is nonnegative. -/
def C0Nonneg (C0 : ℝ) : Prop := 0 ≤ C0

theorem C0Nonneg_iff (C0 : ℝ) : C0Nonneg C0 ↔ 0 ≤ C0 := Iff.rfl

/-- If `V <= A + C0` and `C0 >= 0`, then `V <= A + C0` trivially; record the
weaker `V <= A + C0` consumer so downstream can insert nonneg C0. -/
theorem hullBound_of_C0Nonneg {V A C0 : ℝ}
    (h : V ≤ A + C0) (hC : C0Nonneg C0) : V ≤ A + C0 := h

end LeanFormal.IUT.XiFPaper.Mzk1C0NonnegInterfaceActual