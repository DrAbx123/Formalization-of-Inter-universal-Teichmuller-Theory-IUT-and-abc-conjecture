/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2ComparisonChainActual

def rows : List (String × String × String) :=
  [
  ("R1.3", "R_exact >= 0; R = c0RemainderV2 + correction", "PROVED"),
  ("R1.2", "rank-one/pure tensor/multi-label finite sums integral", "PROVED"),
  ("source q reading", "native magnitude = -log‖qhat‖", "PROVED"),
  ("same-origin landing", "not constructed", "GAP"),
  ("paper comparison", "requires same-origin landing", "OPEN")
  ]

theorem rows_length : rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P2ComparisonChainActual

end
