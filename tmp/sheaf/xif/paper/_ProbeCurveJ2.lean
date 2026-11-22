import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
open LeanFormal.IUT.IUTII.Frobenioid.Example36
example : curveY2EqX3SubX.j = (1728 : ℚ) := by
  norm_num [curveY2EqX3SubX, WeierstrassCurve.j, WeierstrassCurve.c₄, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
