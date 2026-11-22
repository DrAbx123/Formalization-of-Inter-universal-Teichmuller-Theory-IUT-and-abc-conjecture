import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1QVProductRegionActual
/-- The product-region interface is reused from the green donor
`Mzk1HaarProductStrictMainlineActual`: `rpRegion`/`fullRegion`, their measure
positivity/finiteness, strictness, and `rpRadius` already contains `qVFamTensorP`.
This file records the donor names; it does not re-prove or replace them. -/
def productRegionDonorNames : List String :=
  [ "rpRegion", "fullRegion", "rpRadius", "qVFamTensorP",
    "rpRegion_measure_pos", "rpRegion_measure_lt_top",
    "rpRegion_measure_lt_full", "rp_cor312" ]
theorem productRegionDonorNames_length :
    productRegionDonorNames.length = 8 := rfl
#check LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual.rpRegion
#check LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual.rpRegion_measure_pos
#check LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual.rpRegion_measure_lt_top
#check LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual.rpRadius
end LeanFormal.IUT.XiFPaper.Mzk1QVProductRegionActual
end