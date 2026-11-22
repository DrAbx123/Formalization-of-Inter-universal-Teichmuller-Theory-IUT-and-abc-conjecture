import tmp.sheaf.xif.paper.S2483AlgClosedTorsionActual
import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual
import tmp.sheaf.xif.paper.S1493KSideTateTransportActual
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual

noncomputable section
set_option maxHeartbeats 8000000
open WeierstrassCurve Polynomial
namespace LeanFormal.IUT.XiFPaper.S2484LFTorsionActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2483AlgClosedTorsionActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev S2484K (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type := LF T b
abbrev S2484W (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) :
    WeierstrassCurve (S2484K T b) :=
  ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LF T b))

example : (S2484W T b).IsElliptic := by
  unfold S2484W
  infer_instance

#check S2483ThreeDistinctRoots

end LeanFormal.IUT.XiFPaper.S2484LFTorsionActualAdapted
end