import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi gap tightness calibration

Explicit delta/epsilon calibration data for the Stage-5 two-gap adapter. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGapTightnessCalibrationActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

structure StepXIGapTightness where
  epsilon : Real
  delta : Real
  epsilon_pos : 0 < epsilon
  delta_pos : 0 < delta
  delta_sq_le : (1 + delta) ^ 2 ≤ 1 + epsilon

def calibrationHalf : StepXIGapTightness where
  epsilon := 1 / 2
  delta := 1 / 8
  epsilon_pos := by norm_num
  delta_pos := by norm_num
  delta_sq_le := by norm_num

def calibrationOne : StepXIGapTightness where
  epsilon := 1
  delta := 1 / 4
  epsilon_pos := by norm_num
  delta_pos := by norm_num
  delta_sq_le := by norm_num

theorem calibration_exists (ε : Real) (hε : 0 < ε) :
    ∃ δ : Real, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + ε :=
  exists_delta_sq_le_one_add hε

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGapTightnessCalibrationActual

end
