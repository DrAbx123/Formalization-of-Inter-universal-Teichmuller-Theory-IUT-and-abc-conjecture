import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierSingletonReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312PointwiseMembershipWeakening
import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual

/-! Mainline (T3/T1): frontier forms => bridge interface inhabitation and per-epsilon
  comparison families (new consumers completing frontier -> interface -> ABC chain). -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1FrontierToBridgeChainActual

open LeanFormal.IUT

universe u

theorem nonempty_bridgeInterface_of_frontierGapReduced
    (h : ABCFrontierGapReduced.{u}) :
    Nonempty (Cor312ToABCBridgeInterface.{u}) :=
  ⟨bridgeInterface_of_frontierGapReduced h⟩

theorem nonempty_bridgeInterface_of_frontierPointwiseWeakened
    (h : ABCFrontierPointwiseWeakened.{u}) :
    Nonempty (Cor312ToABCBridgeInterface.{u}) :=
  ⟨bridgeInterface_of_frontierPointwiseWeakened h⟩

theorem nonempty_bridgeInterface_of_frontierGapReducedV2
    (h : ABCFrontierGapReducedV2.{u}) :
    Nonempty (Cor312ToABCBridgeInterface.{u}) :=
  ⟨bridgeInterface_of_frontierGapReducedV2 h⟩

def comparisonFamily_of_frontierGapReduced (h : ABCFrontierGapReduced.{u}) :
    ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (bridgeInterface_of_frontierGapReduced h).hullData epsilon :=
  (bridgeInterface_of_frontierGapReduced h).epsilonComparison

end LeanFormal.IUT.XiFPaper.Mzk1FrontierToBridgeChainActual