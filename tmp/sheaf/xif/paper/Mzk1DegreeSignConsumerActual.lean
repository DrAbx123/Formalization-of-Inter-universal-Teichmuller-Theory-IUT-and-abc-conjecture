/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7: sign consumer for `volume = -degree` -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1DegreeSignConsumerActual

/-- If volume is nonpositive and equals `-degree`, the degree is nonnegative. -/
theorem degree_nonneg_of_volume_nonpos {volume degree : ℝ}
    (hv : volume ≤ 0) (h : volume = -degree) : 0 ≤ degree := by
  linarith

/-- If degree is nonnegative, the volume is nonpositive under `volume = -degree`. -/
theorem volume_nonpos_of_degree_nonneg {volume degree : ℝ}
    (hd : 0 ≤ degree) (h : volume = -degree) : volume ≤ 0 := by
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1DegreeSignConsumerActual