/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeHaarScaleActual
def logScale (thetaRead nativeThetaRead : Real) : Real := thetaRead - nativeThetaRead
theorem logScale_eq : logScale thetaRead nativeThetaRead = thetaRead - nativeThetaRead := rfl
def rows : List String := ["explicit log scale = thetaRead - nativeThetaRead", "scale=0 closes theta bridge", "landing still needed for native L block"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeHaarScaleActual
end
