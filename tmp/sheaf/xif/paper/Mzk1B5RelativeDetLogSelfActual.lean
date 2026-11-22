/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogSelfActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
variable {k : Type} [Field k] [NumberField k]
theorem relativeDetLog_self (H : LineBundle (k := k)) (hH : H ≠ 0) :
    relativeDetLog (k := k) H H = 0 := by
  unfold relativeDetLog
  have hone : relativeDetLine (k := k) H H = 1 := by
    unfold relativeDetLine
    rw [determinantLine_eq, determinantLine_eq, mul_inv_cancel₀ hH]
  rw [hone, globalLogVolume_one]


end LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogSelfActual
