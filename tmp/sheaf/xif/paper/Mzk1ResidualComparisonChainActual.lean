import tmp.sheaf.xif.paper.S3131PaperRouteSkeletonActual
import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual

/-! Mainline: comparison-family/bridge chain consumers from the S3131 paper-route
  residual data (new packaging of the residual data into the comparison family form). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ResidualComparisonChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual

universe u

theorem comparisonFamilyV2_of_paperRouteResidualData {X : Type u}
    {W : IQHullLogVolumeInterface X} (R : PaperRouteResidualData W) :
    ∀ epsilon : Real, 0 < epsilon →
      LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.Cor312EpsilonArithmeticComparisonV2
        W epsilon :=
  fun epsilon hepsilon => comparisonOfResiduals R epsilon hepsilon

theorem bridgeInterfaceV2_of_paperRouteResidualData {X : Type u}
    {W : IQHullLogVolumeInterface X} (R : PaperRouteResidualData W) :
    Nonempty (LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.Cor312ToABCBridgeInterfaceV2.{u}) :=
  ⟨bridgeOfResiduals R⟩

theorem heightBound_of_paperRouteResidualData {X : Type u}
    {W : IQHullLogVolumeInterface X} (R : PaperRouteResidualData W) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.cor312ToABCBridge_heightBoundV2
    (bridgeOfResiduals R)

theorem abcConjecture_of_paperRouteResidualData {X : Type u}
    {W : IQHullLogVolumeInterface X} (R : PaperRouteResidualData W) :
    ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.cor312ToABCBridge_abcConjectureV2
    (bridgeOfResiduals R)

end LeanFormal.IUT.XiFPaper.Mzk1ResidualComparisonChainActual