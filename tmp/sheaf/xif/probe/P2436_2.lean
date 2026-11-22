import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2414ThreePointsDistinctActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
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

namespace Probe2436

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev FvCurve : WeierstrassCurve (Fv T b) := (T.arithmetic.curve.baseChange (Fv T b)).curve

example : (FvCurve T b).IsElliptic := inferInstance

example : S2411WK (FvCurve T b) = (WFproj T b).toAffine := rfl

example : (2 : Fv T b) ≠ 0 := by norm_num
example : (2 : LF T b) ≠ 0 := by norm_num

example : ∃ x y z : AlgebraicClosure (Fv T b), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots ∧
    y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots ∧
    z ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots :=
  S2376ThreeDistinctRoots (FvCurve T b) (by norm_num : (2 : Fv T b) ≠ 0)

noncomputable def Pt (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    (S2411WK (FvCurve T b)).toAffine.Point :=
  S2354Point (S2411WK (FvCurve T b)) (by norm_num : (2 : AlgebraicClosure (Fv T b)) ≠ 0) x
    (S2405_eval_zero_of_mem (FvCurve T b) x hx)

example (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • Pt T b x hx = 0 := by
  classical
  exact S2358_two_nsmul (S2411WK (FvCurve T b)) (by norm_num : (2 : AlgebraicClosure (Fv T b)) ≠ 0) x
    (S2405_eval_zero_of_mem (FvCurve T b) x hx)

example (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    Pt T b x hx ≠ 0 := by
  classical
  exact S2414_point_ne_zero (FvCurve T b) (by norm_num : (2 : AlgebraicClosure (Fv T b)) ≠ 0) x hx

noncomputable def Q (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    SideFPoint T b := by
  classical
  exact (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm (Pt T b x hx)

noncomputable def R (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    SideKPoint T b :=
  pointTransport T b (Q T b x hx)

example (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • R T b x hx = 0 := by
  classical
  have hPt : (2 : Nat) • Pt T b x hx = 0 := S2358_two_nsmul (S2411WK (FvCurve T b))
    (by norm_num : (2 : AlgebraicClosure (Fv T b)) ≠ 0) x (S2405_eval_zero_of_mem (FvCurve T b) x hx)
  have hQ : (2 : Nat) • Q T b x hx = 0 := by
    rw [Q]
    rw [(map_nsmul ((WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm) 2 (Pt T b x hx)).symm, hPt, map_zero]
  rw [R]
  rw [(map_nsmul (pointTransport T b) 2 (Q T b x hx)).symm, hQ, map_zero]

example (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    R T b x hx ≠ 0 := by
  classical
  have hPt : Pt T b x hx ≠ 0 := S2414_point_ne_zero (FvCurve T b)
    (by norm_num : (2 : AlgebraicClosure (Fv T b)) ≠ 0) x hx
  have hQ : Q T b x hx ≠ 0 := by
    intro h0
    apply hPt
    have h1 : (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm (Pt T b x hx) = 0 := h0
    have h2 := congrArg (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)) h1
    simpa [Q] using h2
  intro h0
  exact hQ ((pointTransport T b).injective (by simpa [R] using h0))

end Probe2436
end
