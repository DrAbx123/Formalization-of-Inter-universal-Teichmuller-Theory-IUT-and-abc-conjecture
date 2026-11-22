/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#3: chain det degree = normalized volume = degree -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33SourceChainActual

/-- If det arithmetic degree = normalized log-volume and that = our degree,
then det arithmetic degree = our degree (the (Ob3-3) alignment). -/
theorem detDegree_eq_degree {det norm degree : ℝ}
    (hsrc : det = norm) (hdeg : norm = degree) : det = degree := by
  rw [hsrc, hdeg]

/-- Conditional alignment in the other direction: degree = normalized = det. -/
theorem degree_eq_detDegree {det norm degree : ℝ}
    (hsrc : det = norm) (hdeg : degree = norm) : degree = det := by
  rw [hdeg, hsrc]

end LeanFormal.IUT.XiFPaper.Mzk1Ob33SourceChainActual