import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

set_option backward.isDefEq.respectTransparency false
noncomputable section
open WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace ProbeTorsion

theorem Torsion23Rational_congr_curve {F : Type} [Field F]
    {X Y : PuncturedEllipticCurve F} (h : X.curve = Y.curve) :
    PuncturedEllipticCurve.Torsion23Rational X ↔
      PuncturedEllipticCurve.Torsion23Rational Y := by
  cases X with
  | mk curve isElliptic puncture =>
  cases Y with
  | mk curve' isElliptic' puncture' =>
  simp only at h
  subst h
  rfl

theorem iterated_curve_eq
    [Algebra S1687Field S1720Field] [IsScalarTower ℚ S1687Field S1720Field] :
    ((S1667Punctured.baseChange S1687Field).baseChange S1720Field).curve =
      S1720Curve.curve := by
  simp only [PuncturedEllipticCurve.baseChange_curve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_map]
  congr 1
  ext x
  exact (IsScalarTower.algebraMap_apply ℚ S1687Field S1720Field x).symm

end ProbeTorsion