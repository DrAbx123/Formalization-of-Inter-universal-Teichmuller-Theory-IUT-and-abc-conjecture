import Mathlib

/-!
# Mzk1Cor312BoundsV2Actual — Cor 3.12 bound arithmetic (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Hull log-volume + determinant log-volume + nonnegative slack; combined bound theorems. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312BoundsV2Actual

/-- Cor 3.12 bound data: hull and determinant log-volumes plus nonnegative slack. -/
structure Cor312Bounds where
  hullLogVolume : ℚ
  determinantLogVolume : ℚ
  slack : ℚ
  slack_nonneg : 0 ≤ slack

/-- Combined hull+determinant log-volume. -/
def Cor312Bounds.combined (d : Cor312Bounds) : ℚ :=
  d.hullLogVolume + d.determinantLogVolume

/-- Genuine theorem: a value bounded by the combined bound is bounded by combined+slack. -/
theorem combined_le_add_slack {d : Cor312Bounds} {value : ℚ}
    (h : value ≤ d.combined) : value ≤ d.combined + d.slack :=
  le_trans h (le_add_of_nonneg_right d.slack_nonneg)

/-- Genuine theorem: nonnegative components give nonnegative combined bound. -/
theorem combined_nonneg {d : Cor312Bounds}
    (hh : 0 ≤ d.hullLogVolume) (hd : 0 ≤ d.determinantLogVolume) :
    0 ≤ d.combined :=
  add_nonneg hh hd

/-- Genuine theorem: combined bound is monotone in both components. -/
theorem combined_mono {d1 d2 : Cor312Bounds}
    (hh : d1.hullLogVolume ≤ d2.hullLogVolume)
    (hd : d1.determinantLogVolume ≤ d2.determinantLogVolume) :
    d1.combined ≤ d2.combined :=
  add_le_add hh hd

end LeanFormal.IUT.XiFPaper.Mzk1Cor312BoundsV2Actual
