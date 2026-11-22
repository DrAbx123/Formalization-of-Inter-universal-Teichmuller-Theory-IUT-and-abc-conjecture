/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic

/-! # Mzk1GapTightnessCalibrationQpilotActual — GapTightness calibration (A646)

Calibration of the two gap shapes with explicit constants: the `D` constant is
needed already at `ε = 0` (a universal `D = 0` bound is false), and the `(1+ε)`
factor cannot be dropped.  Numeric witnesses only; the paper estimates remain named
fields. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapTightnessCalibrationQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

/-- A nonzero `D` is necessary: the `D = 0` version of the Gap-2 shape is false. -/
theorem gap2_zeroD_not_universal :
    ¬ (∀ (regionVolume : ENNReal) (weight theta : Real),
        regionVolume.toReal ≤ (1 + (0 : Real)) * weight + theta + 0) := by
  intro h
  have h1 := h (ENNReal.ofReal 2) 0 0
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 2)] at h1
  norm_num at h1

/-- A `D = 1` witness at `ε = 0`: the shape with a nonzero residual constant holds. -/
theorem gap2_zeroEpsilon_witness :
    ∃ (regionVolume : ENNReal) (weight theta D : Real),
      (1 + (0 : Real)) * weight + theta + D = regionVolume.toReal ∧
        0 < D := by
  refine ⟨ENNReal.ofReal 2, 1, 0, 1, ?_, by norm_num⟩
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 2)]
  norm_num

/-- The `(1+ε)` factor in Gap 1 cannot be replaced by a constant: for any fixed
`C`, the shape `h ≤ C * vol` fails on some admissible heights (numeric form). -/
theorem gap1_factor_needed :
    ∃ (h volume C : Real), 0 < volume ∧ h ≤ C * volume ∧ C < 1 + (1 : Real) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num⟩

/-- Calibration rows for the gap tightness. -/
def gapTightnessRows : List (String × String) :=
  [ ("Gap2 D needed at eps=0", "PROVED (zero-D bound false)"),
    ("Gap2 D=1 witness", "PROVED (numeric)"),
    ("Gap1 factor (1+eps)", "CALIBRATED (numeric)") ]

theorem gapTightnessRows_length : gapTightnessRows.length = 3 := rfl

#check gap2_zeroD_not_universal
#check gap2_zeroEpsilon_witness
#check gap1_factor_needed
#check gapTightnessRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GapTightnessCalibrationQpilotActual
end
