/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT: GAP-P7-HULL-UB C0 status (paper regime vs general) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBC0ObstacleRowsActual
structure C0ObstacleRow where
  item : String
  status : String
def c0ObstacleRows : List C0ObstacleRow :=
  [ ⟨"paper V = normalizedLog + 1", "PROVED (raw binding)"⟩,
    ⟨"normalizedLog <= 0", "PROVED (hull subset unit)"⟩,
    ⟨"paper regime disc>=2 & cond>=1 & l>=5 => paperBox>=1", "PROVED"⟩,
    ⟨"paper regime => C0=0", "PROVED (paperV_le_paperBox_zero_of_disc_ge_two_cond_ge_one)"⟩,
    ⟨"general CurveData disc=1/cond=1", "OPEN; then paperBox>=1 not automatic"⟩ ]
theorem c0ObstacleRows_length : c0ObstacleRows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBC0ObstacleRowsActual
end