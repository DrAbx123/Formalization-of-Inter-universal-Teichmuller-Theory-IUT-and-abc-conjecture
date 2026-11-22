/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT: input alignment gap rows -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentGapRowsActual
structure AlignGapRow where
  item : String
  status : String
def alignGapRows : List AlignGapRow :=
  [ ⟨"V equivalence NativePlaces ≃ FinitePrimePlace", "GAP: types differ"⟩,
    ⟨"initial equality", "GAP"⟩,
    ⟨"family index equivalence", "GAP"⟩,
    ⟨"OriginalInput equality", "GAP"⟩,
    ⟨"PActual transport", "conditional theorem provided"⟩ ]
theorem alignGapRows_length : alignGapRows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1InputAlignmentGapRowsActual
end