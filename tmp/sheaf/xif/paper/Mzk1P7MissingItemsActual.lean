/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7: still-missing items list (audit-only) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P7MissingItemsActual

def stillMissingItems : List String :=
  [ "#1 general qTheta comparison (paper normalization)" ,
    "#4 multiradial production of (xi-e)/(xi-f) comparison data" ,
    "#6 StepXIContract evidence fields/linkage" ,
    "#7 exact hull volume upper bound V <= (1/4) l (log d + log f) + C0" ]

theorem stillMissingItems_length : stillMissingItems.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7MissingItemsActual