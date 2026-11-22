/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 status record (no axiom/sorry) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1UnitMassNormalizationBridgeActual
def rows : List (String × String) :=
  [    ("det-Haar bridge", "GAP: needs det-Haar law / scale factor from qpilot donor"),
    ("unitMass factor", "green: actualUnitMassENN = ∏ c_b (conditional SigmaFinite)"),
    ("normalized scalar", "c⁻¹*actual=1 follows from factor theorem", "conditional")]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1UnitMassNormalizationBridgeActual
