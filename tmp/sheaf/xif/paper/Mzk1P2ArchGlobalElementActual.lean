/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2ArchGlobalElementActual

def rows : List (String × String × String) :=
  [
  ("GAP", "global arch f construction", "per-place archCK green; global shared-container element not constructed"),
  ("note", "paperBox relation", "arch term excluded from finite HULL-UB")
  ]

theorem rows_length : rows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P2ArchGlobalElementActual

end
