import tmp.sheaf.xif.paper.Mzk1StepXIGapTightnessCalibrationActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi gap-tightness thin re-export

Thin re-export of the green calibration data. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGapTightnessThinReExportActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGapTightnessCalibrationActual

theorem stepxi_calibration_half : StepXIGapTightness := calibrationHalf

theorem stepxi_calibration_one : StepXIGapTightness := calibrationOne

theorem stepxi_calibration_exists (ε : Real) (hε : 0 < ε) :
    ∃ δ : Real, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + ε :=
  calibration_exists ε hε

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGapTightnessThinReExportActual

end
