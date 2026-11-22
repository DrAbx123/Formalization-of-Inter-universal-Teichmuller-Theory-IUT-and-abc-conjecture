import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer

/-! # S3131 (c) wiring: additive point bound -> gap-2 conditional theorem (prior art) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131Gap2AdditiveWiringActual

def S3131Gap2AdditiveWiring : List (String × String) :=
  [ ("Cor312ComparisonGapReduction:306", "cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound = gap2 reduction (hunit + hsplit + hptfin + hpoint)"),
    ("Cor312ComparisonGapReduction:409 hsplit_of_mem_unitRegion", "split-point bound producer from membership in unit region"),
    ("Cor312ComparisonGapReduction:432 hptfin_of_mem_unitRegion", "point-finiteness producer"),
    ("Cor312ComparisonGapReduction:455 pointBound_of_singletonVolume_le_logHeight", "point bound from singleton volume vs log-height"),
    ("Cor312ComparisonGapReduction:525 valuation-bound point bound; :599 additive-input assembly", "alternative point-bound inputs"),
    ("Cor312GapDictionaryLayer:368/:372 cor312GapDict_sourcePointBound_of_additiveBound", "APPROVED ADDITIVE input for hpoint (use instead of refuted hval)") ]

theorem S3131Gap2AdditiveWiring_length : S3131Gap2AdditiveWiring.length = 6 := rfl

#check cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
-- #check (prior-art name to verify later): pointBound_of_singletonVolume_le_logHeight
-- #check (prior-art name to verify later): cor312GapDict_sourcePointBound_of_additiveBound

end LeanFormal.IUT.XiFPaper.S3131Gap2AdditiveWiringActual
end