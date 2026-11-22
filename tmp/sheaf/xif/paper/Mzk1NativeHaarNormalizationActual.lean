/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 status record (no axiom/sorry) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeHaarNormalizationActual
def rows : List (String × String) :=
  [    ("rootUnitMass", "green: local unit-ball mass pos/finite"),
    ("normalizedRootExtensionHaar", "green conditional: unit ball mass=1"),
    ("normalizedProduct_unitBall", "green under SigmaFinite", "conditional")]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeHaarNormalizationActual
