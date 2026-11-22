import tmp.sheaf.xif.paper.S3131PaperRouteAssemblyActual

/-! # S3131 paper-route: ABC from the two field families (no card-P hypothesis) -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteAssemblyActual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteABCBridgeActual

universe u

/-- **Paper-route conditional ABC from the concrete field statements** (b)+(c).
Card P is not a hypothesis: it is the derived strength classification. -/
theorem paperRouteABC_of_families {X : Type u}
    {W : IQHullLogVolumeInterface X} (pt : Nat → Nat → Nat → X)
    (hh : HeightComparisonFamily W pt) (hr : RegionVolumeFamily W pt) :
    ABCConjecture :=
  abcConjecture_of_paperRouteResiduals
    (paperRouteResidualData_of_families pt hh hr)

#check paperRouteABC_of_families

end LeanFormal.IUT.XiFPaper.S3131PaperRouteABCBridgeActual
end