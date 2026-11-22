/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 second wave status record -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1UnitMassNormalizationRowsActual
def rows : List (String × String) :=
  [    ("normalized local", "unit ball mass=1 conditional"),
    ("normalized product", "=1 conditional SigmaFinite"),
    ("unconditional", "GAP")]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1UnitMassNormalizationRowsActual
