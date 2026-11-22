/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperNormalizationRawVsNormalizedActual
import Mathlib.Tactic
/-! # GAP-P6-C17-THETA-S3137 layer 3: raw = scale*norm + offset -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVLayerScaleOffsetActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationRawVsNormalizedActual
structure ThetaVScaleOffset where
  rawV : Real
  normV : Real
  scale : Real
  scale_pos : 0 < scale
  offset : Real
  layer_eq : rawV = scale * normV + offset
theorem rawV_eq (D : ThetaVScaleOffset) :
    D.rawV = D.scale * D.normV + D.offset := D.layer_eq
def rows : List String := ["rawV", "normV", "scale+pos", "offset", "layer_eq (NAMED)"]
theorem rows_length : rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1ThetaVLayerScaleOffsetActual
end