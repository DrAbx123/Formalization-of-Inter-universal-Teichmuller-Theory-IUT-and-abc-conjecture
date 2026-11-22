/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 second wave status record -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902CarrierRflActual
def rows : List (String × String) :=
  [    ("C3 block", "ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple"),
    ("S1902 carrier", "root extension product"),
    ("relation", "GAP: no defeq")]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3S1902CarrierRflActual
