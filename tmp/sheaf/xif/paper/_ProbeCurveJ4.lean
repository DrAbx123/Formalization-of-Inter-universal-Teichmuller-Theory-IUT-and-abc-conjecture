import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
example : (curveY2EqX3SubX.baseChange GaussianField).j = (1728 : GaussianField) := by
  change (curveY2EqX3SubX.map (algebraMap ℚ GaussianField)).j = (1728 : GaussianField)
  rw [WeierstrassCurve.map_j]
  norm_num [curveY2EqX3SubX, WeierstrassCurve.j, WeierstrassCurve.c₄, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
