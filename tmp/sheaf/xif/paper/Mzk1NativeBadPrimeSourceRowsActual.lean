/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 second wave status record -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeSourceRowsActual
def rows : List (String × String) :=
  [    ("reduction", "NativeBadPrimeData <= NativeBadModuliFixedPrime"),
    ("source", "GAP: Bad only odd residue char")]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeSourceRowsActual
