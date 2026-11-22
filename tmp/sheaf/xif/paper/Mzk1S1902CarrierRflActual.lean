/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 second wave status record -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1S1902CarrierRflActual
def rows : List (String × String) :=
  [    ("S1902Carrier", "RootExtensionProductCarrier T = (b:Bad)→rootNormedExtension T b"),
    ("rfl", "definitional alias")]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1S1902CarrierRflActual
