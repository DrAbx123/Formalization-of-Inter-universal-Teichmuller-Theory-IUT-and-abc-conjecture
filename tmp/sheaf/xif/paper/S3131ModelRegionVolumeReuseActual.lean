import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel

/-! # S3131 model region volume prior-art reuse map - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131ModelRegionVolumeReuseActual

def S3131ModelRegionVolumeReuse : List (String × String) :=
  [ ("IQCarrierConcreteModel.lean:328 iqCarrierModelLogVolume_region_eq", "concrete comparison region = log-shell + point; volume = ofReal pointWeight -> REUSE for model (c)/(b) region-volume side"),
    ("IQCarrierConcreteModel.lean:166 iqCarrierModelLogVolume_union_le", "subadditivity over union -> REUSE for region vs hull decomposition"),
    ("IQCarrierConcreteModel.lean:531 iqCarrierModel_hmem_hweightvol_incompatible", "shell-membership vs weight-volume incompatibility -> REUSE as a warning constraint for (a)/(b) point placement"),
    ("normalizedComparisonRegion (Cor312ToABCBridgeInterface.lean:201)", "priori-art region construction scaleShift '' (unitRegion ∪ {point}) -> ADOPT in our V2 (a)"),
    ("CardAMPLThetaBoundSupply:78/94/101/109/116", "hull upper-bound supply -> REUSE for hull finiteness/upper bound"),
    ("CardHullRealSignedLogVolume:114/129/143/155/176/204/259", "SIGNED Theta readout + hull/image volume comparison -> REUSE/ADAPT") ]

theorem S3131ModelRegionVolumeReuse_length : S3131ModelRegionVolumeReuse.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131ModelRegionVolumeReuseActual