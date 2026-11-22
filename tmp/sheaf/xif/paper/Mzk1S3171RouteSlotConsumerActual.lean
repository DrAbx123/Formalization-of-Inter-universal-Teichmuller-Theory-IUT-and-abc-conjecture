import tmp.sheaf.xif.paper.AbsTopIII05RefinedActual
import tmp.sheaf.xif.paper.Mzk1PaperRouteResidualChainActual
import tmp.sheaf.xif.paper.S3131PaperRouteSkeletonActual
import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual

/-! Mainline/routes: turn the S3171 route slot (AbsTopIII05 refined consumption point)
  into the S3131 paper-route residual data and the V2 bridge interface. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1S3171RouteSlotConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.AbsTopIII05RefinedActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperRouteResidualChainActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

universe u

theorem paperRouteResidualData_of_s3171RouteSlot {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    {T : Thm110DisplayTerms} (S : S3171RouteSlot X W pt T) :
    PaperRouteResidualData W :=
  paperRouteResidualData_of_undilatedBounds W pt S.heightBound S.regionBound

theorem nonempty_bridgeInterfaceV2_of_s3171RouteSlot {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    {T : Thm110DisplayTerms} (S : S3171RouteSlot X W pt T) :
    Nonempty (LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.Cor312ToABCBridgeInterfaceV2.{u}) :=
  ⟨bridgeOfResiduals (paperRouteResidualData_of_s3171RouteSlot S)⟩

theorem abcConjecture_of_s3171RouteSlot_residual {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    {T : Thm110DisplayTerms} (S : S3171RouteSlot X W pt T) :
    ABCConjecture :=
  abcConjecture_of_paperRouteResiduals (paperRouteResidualData_of_s3171RouteSlot S)

end LeanFormal.IUT.XiFPaper.Mzk1S3171RouteSlotConsumerActual