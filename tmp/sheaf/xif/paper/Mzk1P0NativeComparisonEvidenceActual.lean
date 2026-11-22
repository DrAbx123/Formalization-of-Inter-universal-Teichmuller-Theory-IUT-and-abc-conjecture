/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonEvidenceActual
def rows : List String := ["NativeComparison := nativeQReadout <= nativeThetaReadout", "sufficient: theta readout >= 0", "native comparison not proved", "evidence rows only"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonEvidenceActual
end
