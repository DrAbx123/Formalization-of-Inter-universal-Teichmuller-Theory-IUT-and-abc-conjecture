import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

/-! # S3131 prior-art: (c) Gap-2 reduction ALREADY EXISTS (reuse, no rebuild) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131Gap2ReductionReuseActual

def S3131Gap2ReuseLines : List (String × String) :=
  [ ("Cor312ComparisonGapReduction.lean:306", "cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound = the (c) interface (regionVolume_le_normalizedWeight from split-point bound + unit-region bound) -> USE DIRECTLY"),
    ("Cor312ComparisonGapReduction.lean:55/:127 docs", "gap2 reduction docs -> citation"),
    ("Cor312ComparisonGapReduction.lean:359/:391 usage", "usage sites -> pattern reuse"),
    ("Cor312GapDictionaryLayer.lean:34/:39/:368", "split-point/unit-region bound obligations (dictionary layer) -> exact remaining hypotheses"),
    ("Cor312ComparisonGapSupplyLayer.lean:271", "Gap supply layer -> prior-art supply shape") ]

theorem S3131Gap2ReuseLines_length : S3131Gap2ReuseLines.length = 5 := rfl

#check cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound

end LeanFormal.IUT.XiFPaper.S3131Gap2ReductionReuseActual
end