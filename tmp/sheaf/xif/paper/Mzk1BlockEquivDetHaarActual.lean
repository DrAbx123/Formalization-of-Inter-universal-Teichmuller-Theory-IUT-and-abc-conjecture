/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 second wave status record -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BlockEquivDetHaarActual
def rows : List (String × String) :=
  [    ("det-Haar", "Haar transport factor for blockEquiv"),
    ("status", "GAP")]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1BlockEquivDetHaarActual
