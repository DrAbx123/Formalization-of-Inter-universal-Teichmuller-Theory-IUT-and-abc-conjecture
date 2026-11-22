/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullUpperBoundInterfaceActual
import Mathlib.Tactic

/-! # P7/#7: concrete C0 candidates satisfying the hull upper-bound interface -/

/-
| field | value |
|---|---|
| Status | PROVED: under `main >= 0`, `C0 = |V|` and `C0 = V` satisfy the bound; no actual V/C0 source object yet |
| GAP | GAP-P7-HULL-UB: actual V and the paper constant C0 are still not constructed |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1HullC0CandidateActual

open LeanFormal.IUT.XiFPaper.Mzk1HullUpperBoundInterfaceActual

/-- `C0 = |V|` works when the main term is nonnegative. -/
theorem hullUpperBound_abs_C0 {V l d f : ℝ}
    (hmain : 0 ≤ (1 / 4) * l * (Real.log d + Real.log f)) :
    HullUpperBound V l d f |V| := by
  unfold HullUpperBound
  have hV : V ≤ |V| := le_abs_self V
  linarith

/-- `C0 = V` works when the main term is nonnegative. -/
theorem hullUpperBound_self_C0 {V l d f : ℝ}
    (hmain : 0 ≤ (1 / 4) * l * (Real.log d + Real.log f)) :
    HullUpperBound V l d f V := by
  unfold HullUpperBound
  linarith

/-- With the concrete `C0 = |V|` and a nonnegative main term, `V` is bounded by
`main + |V|`; this is the explicit candidate bound. -/
theorem V_le_main_add_abs {V l d f : ℝ}
    (hmain : 0 ≤ (1 / 4) * l * (Real.log d + Real.log f)) :
    V ≤ (1 / 4) * l * (Real.log d + Real.log f) + |V| := by
  have hV : V ≤ |V| := le_abs_self V
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1HullC0CandidateActual