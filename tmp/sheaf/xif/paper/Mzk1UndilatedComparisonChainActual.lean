import tmp.sheaf.xif.paper.Mzk1PaperRouteResidualChainActual
import tmp.sheaf.xif.paper.Mzk1ResidualComparisonChainActual
import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual

/-! Mainline: direct chain from undilated (b)/(c) bounds to the per-epsilon comparison
  family and bridge interface (composition of the two new constructions). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1UndilatedComparisonChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1PaperRouteResidualChainActual
open LeanFormal.IUT.XiFPaper.Mzk1ResidualComparisonChainActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

universe u

theorem comparisonFamilyV2_of_undilatedBounds {X : Type u}
    (W : IQHullLogVolumeInterface X) (pt : Nat → Nat → Nat → X)
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ∀ epsilon : Real, 0 < epsilon →
      LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.Cor312EpsilonArithmeticComparisonV2
        W epsilon :=
  comparisonFamilyV2_of_paperRouteResidualData
    (paperRouteResidualData_of_undilatedBounds W pt hb hc)

theorem bridgeInterfaceV2_of_undilatedBounds {X : Type u}
    (W : IQHullLogVolumeInterface X) (pt : Nat → Nat → Nat → X)
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    Nonempty (LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.Cor312ToABCBridgeInterfaceV2.{u}) :=
  bridgeInterfaceV2_of_paperRouteResidualData
    (paperRouteResidualData_of_undilatedBounds W pt hb hc)

end LeanFormal.IUT.XiFPaper.Mzk1UndilatedComparisonChainActual