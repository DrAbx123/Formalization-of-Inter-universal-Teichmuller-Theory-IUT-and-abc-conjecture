/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT/GAP: paper V ratio row inventory -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperVRatioRowsActual
structure VRatioRow where
  item : String
  status : String
def rowsData : List VRatioRow :=
  [ ⟨"raw C3 Haar log", "green S3137"⟩,
    ⟨"actual C3 dimension", "green S3137"⟩,
    ⟨"raw/dim ratio", "GAP (paper normalization)"⟩,
    ⟨"paper V factor", "GAP"⟩,
    ⟨"C3-vs-D dimension dictionary", "GAP"⟩ ]
theorem rowsData_length : rowsData.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperVRatioRowsActual
end