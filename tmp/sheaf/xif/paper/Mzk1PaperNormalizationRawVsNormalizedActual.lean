/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # GAP: raw paper V vs normalized log dictionary -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationRawVsNormalizedActual
structure RawNormalizedDictionary where
  rawV : Real
  normV : Real
  scale : Real
  scale_pos : 0 < scale
  offset : Real
  dict_eq : rawV = scale * normV + offset
theorem normV_eq (D : RawNormalizedDictionary) :
    D.normV = (D.rawV - D.offset) / D.scale := by
  field_simp [ne_of_gt D.scale_pos]
  linarith [D.dict_eq]
def RawNormalizedDictionaryRequired : Prop := Nonempty RawNormalizedDictionary
def rows : List String := ["rawV", "normV", "scale+pos", "offset", "dict_eq (NAMED)"]
theorem rows_length : rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationRawVsNormalizedActual
end