/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P6/P7: signed log identities used by the q/theta readings -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedLogIdentityActual

/-- For `x < 0`, `-|x| = x`. -/
theorem neg_abs_eq_self_of_neg {x : ℝ} (hx : x < 0) : -|x| = x := by
  rw [abs_of_neg hx]
  ring

/-- The signed q reading `-|log q|` equals `log q` when `log q < 0`. -/
theorem neg_abs_log_eq_log_of_log_neg {q : ℝ} (hq : 0 < q) (hlt : q < 1) :
    -|Real.log q| = Real.log q := by
  apply neg_abs_eq_self_of_neg
  exact Real.log_neg hq hlt

/-- If the log is negative, `-|log q| <= 0`. -/
theorem signed_log_nonpos_of_log_neg {q : ℝ} (hq : 0 < q) (hlt : q < 1) :
    -|Real.log q| ≤ 0 := by
  rw [neg_abs_log_eq_log_of_log_neg hq hlt]
  exact le_of_lt (Real.log_neg hq hlt)

end LeanFormal.IUT.XiFPaper.Mzk1SignedLogIdentityActual