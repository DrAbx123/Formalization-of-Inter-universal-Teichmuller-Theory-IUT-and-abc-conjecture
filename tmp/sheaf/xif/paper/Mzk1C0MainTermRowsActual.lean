/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT/GAP: C0/mainTerm source rows -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C0MainTermRowsActual
structure C0Row where
  item : String
  source : String
  status : String
def c0Rows : List C0Row :=
  [ ⟨"log d", "CurveData.disc", "actual Nat nonzero; log nonneg proved"⟩,
    ⟨"log f", "CurveData.cond / primeConductorLogDisc", "log nonneg proved"⟩,
    ⟨"mainTerm nonneg", "(1/4) l (logd + logf)", "proved (Mzk1MainTermActualNonnegActual)"⟩,
    ⟨"V <= mainTerm", "normalizedLog_hull_le_actualMainTerm", "proved (Mzk1MainTermActualBoundActual)"⟩,
    ⟨"C0", "no actual C0 object in tree", "GAP; current bound uses C0=0"⟩ ]
theorem c0Rows_length : c0Rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C0MainTermRowsActual
end