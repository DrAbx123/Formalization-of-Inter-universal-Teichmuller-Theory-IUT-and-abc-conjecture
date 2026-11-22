import LeanFormal.IUT.Audit.Status

/-! # S3131 normalized-volume-comparison prior art map - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131NormalizedVolumeComparisonPriorArtActual

def S3131NormalizedVolumeComparisonPriorArt : List (String × String) :=
  [ ("ThetaBoundToHeightWeight.lean:67 heightWeightBound_of_normalizedVolumeComparison", "PRIOR-ART BRIDGE: (b)+(c) shape hypotheses => height <= (1+eps)*weight + A; reuses exists_oneAdd_sq_le_oneAdd:47; ALREADY used by Cor312ToABCBridgeInterface.cor312ToABCBridge_heightBoundV2 -> REUSE (no new bridge)"),
    ("Cor312ToABCBridgeInterface.lean:201 normalizedComparisonRegion; :224 Cor312EpsilonArithmeticComparison; :256+ bridge", "prior-art region/comparison/bridge -> REUSE/ADAPT"),
    ("Cor312ComparisonGapReduction.lean:128-478", "gap2 reductions, gap1 conditional reduction; uniform refuted -> prior-art gap analysis"),
    ("Cor312GapDictionaryLayer.lean:176-372", "dictionary non-universality + positive reductions -> prior-art"),
    ("IQCarrierHaarData.lean:207 hull finiteness; HunitEpsilonTransferReduction hunit chain", "(c) theta/hull side pieces -> REUSE/ADAPT"),
    ("ABCHeightWeightAdditiveBoundV2", "the ABC-strength bound consumed downstream; (b)+(c) derive the weaker heightWeightBound (not the additive bound itself)") ]

theorem S3131NormalizedVolumeComparisonPriorArt_length : S3131NormalizedVolumeComparisonPriorArt.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131NormalizedVolumeComparisonPriorArtActual