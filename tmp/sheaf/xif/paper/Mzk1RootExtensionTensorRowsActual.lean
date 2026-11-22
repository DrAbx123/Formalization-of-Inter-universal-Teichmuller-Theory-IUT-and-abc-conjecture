/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 second wave status record -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1RootExtensionTensorRowsActual
def rows : List (String × String) :=
  [    ("root tensor", "product/tensor distinction"),
    ("status", "GAP: FinitePadicTensor vs pi")]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1RootExtensionTensorRowsActual
