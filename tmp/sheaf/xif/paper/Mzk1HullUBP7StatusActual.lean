/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT: GAP-P7-HULL-UB status after actual main-term bound -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBP7StatusActual
structure HullUBStatusRow where
  item : String
  status : String
def hullUBRows : List HullUBStatusRow :=
  [ ⟨"normalizedLog hull <= (1/4)l(log disc+log cond)", "PROVED actual (C0=0)"⟩,
    ⟨"normalizedLog hull <= paperBox(disc,cond,0)", "PROVED actual"⟩,
    ⟨"paper V = rawV via dictionary", "CONDITIONAL (RawNormalizedDictionary)"⟩,
    ⟨"GAP-P7-HULL-UB unconditional paper V", "OPEN; only conditional dictionary route"⟩ ]
theorem hullUBRows_length : hullUBRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBP7StatusActual
end