/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT/GAP: paper normalization #2/#5 row inventory -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationRowsActual
structure Row where
  item : String
  status : String
def rowsData : List Row :=
  [ ⟨"raw Haar -> paper V", "GAP"⟩,
    ⟨"[C3 block:Qp] factor", "GAP"⟩,
    ⟨"C3-vs-D dictionary", "GAP"⟩,
    ⟨"paper IQ carrier", "GAP"⟩,
    ⟨"(Ob3-3) source identification", "GAP"⟩,
    ⟨"multiradial comparison", "GAP"⟩ ]
theorem rowsData_length : rowsData.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationRowsActual
end