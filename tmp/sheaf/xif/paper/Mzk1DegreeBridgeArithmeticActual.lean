/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P6/P7: arithmetic for the q-side degree bridge `volume = -degree` -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1DegreeBridgeArithmeticActual

/-- `volume = -degree` is equivalent to `degree = -volume`. -/
theorem volume_eq_neg_degree_iff {volume degree : ℝ} :
    volume = -degree ↔ degree = -volume := by
  constructor <;> intro h <;> linarith

/-- If the q-pilot volume is minus the source bad-q absolute log, the degree is
the bad-q absolute log. -/
theorem degree_eq_of_volume_eq_neg {volume badQ : ℝ}
    (h : volume = -badQ) : -volume = badQ := by
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1DegreeBridgeArithmeticActual