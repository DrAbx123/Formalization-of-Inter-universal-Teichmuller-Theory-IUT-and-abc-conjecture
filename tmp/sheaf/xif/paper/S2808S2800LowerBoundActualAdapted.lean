import tmp.sheaf.xif.paper.S2800LineBundleCor312BridgeActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2808S2800LowerBoundActualAdapted

/-- S2800 bridge data together with the actual S2752 hweightvol lower bound. -/
structure S2808BridgeData (l : PrimeGeFive) (eps : Real) where
  global : S2800GlobalData l
  epsData : S2800EpsData l global eps
  hweightvol : S2736QPilotLineBundleHweightvol (S2752J l) 0

/-- The actual S2752 hweightvol lower bound. -/
theorem S2808_hweightvol :
    S2736QPilotLineBundleHweightvol (S2752J fiveLabel) 0 :=
  S2752_hweightvol fiveLabel

/-- Full conditional bridge with the S2752 lower bound recorded. -/
noncomputable def S2808Bridge (l : PrimeGeFive) (G : S2800GlobalData l)
    (hg : forall eps : Real, 0 < eps ->
      S2800EpsData l G eps) :
    Cor312ToABCBridgeInterface :=
  S2800Bridge l G hg

end LeanFormal.IUT.XiFPaper.S2808S2800LowerBoundActualAdapted
end
