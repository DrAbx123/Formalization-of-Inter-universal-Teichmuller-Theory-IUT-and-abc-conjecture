/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeLSideActual
import tmp.sheaf.xif.paper.Mzk1P0NativeQDonorActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeQReadoutBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
def rows : List String := ["nativeLSideQReadout = donorQReadout", "donorQReadout = nativeQReadout (rfl)", "no concreteQCandidate choice equality"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeQReadoutBridgeActual
end
