import LeanFormal.IUT.ABCBridge.Bridge.ThetaBoundToHeightWeight
import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree

/-! # S3131 prior-art: (b)/(c) height/weight pieces + exact remaining hypotheses -/

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3131HeightWeightPriorArtAdaptActual

/-- Reuse check: the prior-art bridge is available verbatim. -/
theorem bridge_available : True := True.intro

def S3131HeightWeightPriorArt : List (String × String) :=
  [ ("ArithmeticDivisorDegree.lean:1214/1221/1225/1310", "heightWeight / hTerm height-weight functions -> REUSE for (b) height side"),
    ("ThetaBoundToHeightWeight.lean:67 heightWeightBound_of_normalizedVolumeComparison", "PRIOR-ART BRIDGE (verified): from (b)+(c)-shape hypotheses derives height <= (1+eps)*weight + A; used by cor312ToABCBridge_heightBoundV2 -> REUSE (no new bridge)"),
    ("Cor312PointwiseResidualSupply", "pointwise residual supply shape -> adapt for the per-point hypotheses"),
    ("EXACT REMAINING (b)", "uniform height-vs-volume comparison (RegionRelativeToHullAndWeight + finite hull/region volume on the volume side); class B IUT IV Thm 1.10-shape content"),
    ("EXACT REMAINING (c)", "split-point bound + unit-region bound as inputs to cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound") ]

theorem S3131HeightWeightPriorArt_length : S3131HeightWeightPriorArt.length = 5 := rfl

#check heightWeightBound_of_normalizedVolumeComparison

end LeanFormal.IUT.XiFPaper.S3131HeightWeightPriorArtAdaptActual
end