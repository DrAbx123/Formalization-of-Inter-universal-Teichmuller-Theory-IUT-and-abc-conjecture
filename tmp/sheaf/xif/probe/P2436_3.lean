import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2414ThreePointsDistinctActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

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
open LeanFormal.IUT.XiFPaper.S2414ThreePointsDistinctActual

namespace Probe2436b

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev FvCurve : WeierstrassCurve (Fv T b) := (T.arithmetic.curve.baseChange (Fv T b)).curve

example : Nontrivial (AlgebraicClosure (Fv T b)) := inferInstance
example : (S2411WK (FvCurve T b)).toAffine.IsElliptic := inferInstance
example : AddCommGroup (S2411WK (FvCurve T b)).toAffine.Point := inferInstance
example (P : (S2411WK (FvCurve T b)).toAffine.Point) : (2 : Nat) • P = (2 : Nat) • P := rfl

example (P : Affine.Point ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LF T b))) :
    (2 : Nat) • P = (2 : Nat) • P := rfl

-- the cast issue: try to pass a S2411WK-point where an LF-point is expected
example (P : (S2411WK (FvCurve T b)).toAffine.Point) :
    Affine.Point ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LF T b)) := P

end Probe2436b
end
