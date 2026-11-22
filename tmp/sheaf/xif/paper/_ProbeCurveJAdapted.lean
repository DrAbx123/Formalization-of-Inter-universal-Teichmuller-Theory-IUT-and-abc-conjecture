import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilyLawsReduction
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
#check curveY2EqX3SubX
example : curveY2EqX3SubX.j = (1728 : ℚ) := by
  norm_num [WeierstrassCurve.j, WeierstrassCurve.c₄, WeierstrassCurve.Δ, curveY2EqX3SubX]
