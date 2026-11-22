/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 status record (no axiom/sorry) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeDataSourceActual
def rows : List (String × String) :=
  [    ("NativeBadPrimeData", "green conditional: from NativeBadModuliFixedPrime"),
    ("prime equality", "green: nativeBadToKPlace prime = underlying Bad place prime"),
    ("source", "GAP: fixed p on all Bad places")]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeDataSourceActual
