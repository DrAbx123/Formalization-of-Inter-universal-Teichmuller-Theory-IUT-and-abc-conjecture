import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2414ThreePointsDistinctActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxErrors 30

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

namespace Probe2436c

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

local instance : DecidableEq (AlgebraicClosure (Fv T b)) := Classical.decEq _

abbrev FvCurve : WeierstrassCurve (Fv T b) := (T.arithmetic.curve.baseChange (Fv T b)).curve

example : AddCommGroup (S2411WK (FvCurve T b)).toAffine.Point := inferInstance
example : AddCommGroup (Affine.Point ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LF T b))) := inferInstance

noncomputable def Pt (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    (S2411WK (FvCurve T b)).toAffine.Point :=
  S2354Point (S2411WK (FvCurve T b)) (by norm_num : (2 : AlgebraicClosure (Fv T b)) ≠ 0) x
    (S2405_eval_zero_of_mem (FvCurve T b) x hx)

noncomputable def E' : SideFPoint T b ≃+ (WFproj T b).toAffine.Point :=
  WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)

noncomputable def Q (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    SideFPoint T b :=
  (E' T b).symm (Pt T b x hx)

noncomputable def R (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    SideKPoint T b :=
  pointTransport T b (Q T b x hx)

theorem Pt_two (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • Pt T b x hx = 0 := by
  classical
  exact S2358_two_nsmul (S2411WK (FvCurve T b)) (by norm_num : (2 : AlgebraicClosure (Fv T b)) ≠ 0) x
    (S2405_eval_zero_of_mem (FvCurve T b) x hx)

theorem Pt_ne_zero (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    Pt T b x hx ≠ 0 := by
  classical
  exact S2414_point_ne_zero (FvCurve T b) (by norm_num : (2 : AlgebraicClosure (Fv T b)) ≠ 0) x hx

theorem R_two (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • R T b x hx = 0 := by
  classical
  have hP : (2 : Nat) • Pt T b x hx = 0 := Pt_two T b x hx
  show (2 : Nat) • pointTransport T b ((E' T b).symm (Pt T b x hx)) = 0
  rw [(map_nsmul (pointTransport T b) 2 ((E' T b).symm (Pt T b x hx))).symm]
  rw [(map_nsmul (E' T b).symm 2 (Pt T b x hx)).symm]
  rw [hP, map_zero, map_zero]

theorem R_ne_zero (x : AlgebraicClosure (Fv T b))
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b))) (FvCurve T b).twoTorsionPolynomial).roots) :
    R T b x hx ≠ 0 := by
  classical
  have hP : Pt T b x hx ≠ 0 := Pt_ne_zero T b x hx
  intro hR
  have h1 : pointTransport T b ((E' T b).symm (Pt T b x hx)) = pointTransport T b 0 := by
    rw [hR, map_zero]
  have h2 : (E' T b).symm (Pt T b x hx) = 0 := (pointTransport T b).injective h1
  have h4 : (E' T b) ((E' T b).symm (Pt T b x hx)) = (E' T b) 0 := congrArg (E' T b) h2
  rw [AddEquiv.apply_symm_apply, map_zero] at h4
  exact hP h4

end Probe2436c
end
