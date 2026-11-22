import tmp.sheaf.xif.paper.S2480QiActual
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482QiCurveActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual

/-- The curve y^2 = x^3 - x over F = Q(i). -/
def S2482Curve : WeierstrassCurve F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

theorem S2482Curve_Δ : S2482Curve.Δ = 64 := by
  rw [S2482Curve, WeierstrassCurve.Δ]
  norm_num [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : S2482Curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, S2482Curve_Δ]
  norm_num

def S2482PuncturedCurve : PuncturedEllipticCurve F :=
  { curve := S2482Curve
    isElliptic := inferInstance
    puncture := 0 }

example : IsGalois ℚ F := inferInstance
example : IsGalois F F := inferInstance
example : IsScalarTower ℚ F F := inferInstance
example : FiniteDimensional F F := inferInstance
#check S2482Curve
#check S2482Curve_Δ
#check S2482PuncturedCurve
#print axioms S2482Curve_Δ

end LeanFormal.IUT.XiFPaper.S2482QiCurveActual

end