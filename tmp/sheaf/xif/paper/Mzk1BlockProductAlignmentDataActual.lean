/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 second wave status record -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BlockProductAlignmentDataActual
def rows : List (String × String) :=
  [    ("fields", "J ≃ Bad + per-factor E_j ≃ rootNormedExtension + AlgEquiv compatibility"),
    ("inhabitant", "GAP; required as construction data")]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1BlockProductAlignmentDataActual
