import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual
import tmp.sheaf.xif.paper.S3131PaperRouteSkeletonActual

/-! # S3131 paper-route: assemble PaperRouteResidualData from the two field families -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteAssemblyActual

universe u

def paperRouteResidualData_of_families {X : Type u}
    {W : IQHullLogVolumeInterface X} (pt : Nat → Nat → Nat → X)
    (hh : HeightComparisonFamily W pt) (hr : RegionVolumeFamily W pt) :
    PaperRouteResidualData W where
  point := pt
  height_comparison := hh
  region_volume_bound := hr

#check paperRouteResidualData_of_families

end LeanFormal.IUT.XiFPaper.S3131PaperRouteAssemblyActual
end