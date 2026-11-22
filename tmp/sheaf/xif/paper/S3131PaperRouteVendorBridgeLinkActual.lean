import tmp.sheaf.xif.paper.S3131PaperRouteABCBridgeActual
import tmp.sheaf.xif.paper.S3131PaperRouteComparisonDataActual

/-! # S3131 paper route: vendor payload + field families -> ABC -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteABCBridgeActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteComparisonDataActual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteVendorBridgeLinkActual

universe u

/-- Paper-route ABC from the two analytic families, together with the vendor-shaped
signed comparison payload (the payload records the Cor. 3.12 signed endpoints). -/
theorem abc_of_families_and_vendorPayload {X : Type u}
    {W : IQHullLogVolumeInterface X} (pt : Nat → Nat → Nat → X)
    (hh : HeightComparisonFamily W pt) (hr : RegionVolumeFamily W pt)
    (d : S3131PaperRouteComparisonData) : ABCConjecture :=
  paperRouteABC_of_families pt hh hr

#check abc_of_families_and_vendorPayload

end LeanFormal.IUT.XiFPaper.S3131PaperRouteVendorBridgeLinkActual
end