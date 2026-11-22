import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2414ThreePointsDistinctActual

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2411PointBuildActual
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2376ThreeRootsActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual
open LeanFormal.IUT.XiFPaper.S2412ThreePointsTransportActual
open LeanFormal.IUT.XiFPaper.S2414ThreePointsDistinctActual

namespace Probe2436

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

#check @pointTransport
#check Fv
#check LF
#check WFproj
#check WKproj
#check @S2412ThreePoints
#check @S2414_point_ne
#check @S2414_point_ne_zero
#check @S2358_two_nsmul
#check @S2354Point
#check @S2376ThreeDistinctRoots
#check @S2405_eval_zero_of_mem
#check sectionFPlace
#check Completion

example : CharZero (Completion (sectionFPlace T b)) := inferInstance

example : S2411WK ((T.arithmetic.curve.baseChange (Fv T b)).curve)
    = ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LF T b)) := rfl

example (P : WeierstrassCurve.Affine.Point ((S2411WK ((T.arithmetic.curve.baseChange (Fv T b)).curve)).toAffine)) :
    WeierstrassCurve.Affine.Point ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LF T b)) := P

end Probe2436
end
