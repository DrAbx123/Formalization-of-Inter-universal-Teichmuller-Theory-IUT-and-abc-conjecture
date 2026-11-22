import tmp.sheaf.xif.paper.S3131PaperRouteABCBridgeActual
import tmp.sheaf.xif.paper.S3136VendorCor312SchemaAdaptedActual

/-! # S3131 route: ABC from families + stage4 vendor-adapted payload -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteABCBridgeActual
open LeanFormal.IUT.XiFPaper.S3136VendorCor312SchemaAdaptedActual

namespace LeanFormal.IUT.XiFPaper.S3131RoutePayloadLGPWiringActual

universe u

theorem abc_of_families_and_LGPPayload {X : Type u}
    {W : IQHullLogVolumeInterface X} (pt : Nat → Nat → Nat → X)
    (hh : HeightComparisonFamily W pt) (hr : RegionVolumeFamily W pt)
    (d : LGPModelCor312ComparisonData) : ABCConjecture :=
  paperRouteABC_of_families pt hh hr

#check abc_of_families_and_LGPPayload

end LeanFormal.IUT.XiFPaper.S3131RoutePayloadLGPWiringActual
end