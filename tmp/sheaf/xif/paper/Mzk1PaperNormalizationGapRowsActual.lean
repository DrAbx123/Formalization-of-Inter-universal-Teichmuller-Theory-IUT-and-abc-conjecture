/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT: paper normalization raw/normalized gap rows -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationGapRowsActual
structure NormGapRow where
  item : String
  status : String
def normGapRows : List NormGapRow :=
  [ ⟨"raw C3 Haar log", "green S3137"⟩,
    ⟨"normalizedLog hull", "green S1902/Mzk1HullLogVolumeFormula"⟩,
    ⟨"raw-vs-normalized scale", "GAP (paper normalization dictionary)"⟩,
    ⟨"[C3 block:Qp] factor", "GAP"⟩,
    ⟨"paper V identification", "GAP"⟩ ]
theorem normGapRows_length : normGapRows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationGapRowsActual
end