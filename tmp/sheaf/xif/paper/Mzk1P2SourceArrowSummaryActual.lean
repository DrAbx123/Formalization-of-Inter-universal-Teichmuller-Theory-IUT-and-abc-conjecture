/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2SourceArrowSummaryActual

def rows : List (String × String × String) :=
  [
  ("native q image", "c0QHat = algebraMap(qVFamily.q)", "PROVED"),
  ("norm bridge", "‖c0QHat‖=‖qVFamily.q‖", "PROVED"),
  ("reading sign", "localLogMagnitude = -log‖c0QHat‖", "PROVED"),
  ("old C3 reading", "S1429 empty", "GAP"),
  ("same-origin map", "P.line.C3.q vs qVFamily", "GAP")
  ]

theorem rows_length : rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P2SourceArrowSummaryActual

end
