import LeanFormal.IUT.Audit.Status

/-! # S3131 (b) height-vs-volume dictionary attempt: existing pieces + exact remaining hypothesis -/

namespace LeanFormal.IUT.XiFPaper.S3131HeightVolumeDictionaryAttemptActual

def S3131HeightVolumePieces : List (String × String) :=
  [ ("RationalPointDictionary.lean:28-34", "Height.logHeight1 (abcRationalPoint a c) = log c -> REUSE"),
    ("SourceImageHullVolume.lean:103/107/110", "sourceLocalLogDegree/sourcePointVolume/logDegree_one -> REUSE volume side"),
    ("SourceQSideComparison.lean:88", "sourceQSideNormalizedValue -> q-side value"),
    ("EXACT REMAINING (b)", "uniform height-vs-region-volume comparison: exists uniform C, forall ABC triples, Height.logHeight1 (abcRationalPoint a c) <= (W.logVolume {point a b c}).toReal + C (undilated); this is IUT IV Thm 1.10-shape class B content") ]

theorem S3131HeightVolumePieces_length : S3131HeightVolumePieces.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.S3131HeightVolumeDictionaryAttemptActual