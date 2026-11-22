import tmp.sheaf.xif.paper.S2830GluedPointMapActual
import tmp.sheaf.xif.paper.S2821E37ProjectiveOverActual

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2831GluedOverPointMapActual

open LeanFormal.IUT.XiFPaper.S2830GluedPointMapActual
open LeanFormal.IUT.XiFPaper.S2829E37GaussianPointActual
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2828PointRealizationActual
open LeanFormal.IUT.XiFPaper.S2789E37OrbicurveSignActual

local instance : Field K := S2789Arithmetic.fieldF
local instance : DecidableEq K := Classical.decEq _

noncomputable def S2831GluedOverMap
    (x : S2813Base K ⟶ S2821AsOver K) :
    S2829Curve.toProjective.Point :=
  S2830GluedMap (Over.Hom.left x)

noncomputable def S2831ChartZOverPoint (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    S2813Base K ⟶ S2821AsOver K :=
  S2829ChartZOver x y h ≫ S2821ChartZOver K

noncomputable def S2831ChartYInfinityOverPoint :
    S2813Base K ⟶ S2821AsOver K :=
  S2829ChartYInfinityOver ≫ S2821ChartYOver K

#check S2831GluedOverMap
#check S2831ChartZOverPoint
#check S2831ChartYInfinityOverPoint
#print axioms S2831GluedOverMap
#print axioms S2831ChartZOverPoint
#print axioms S2831ChartYInfinityOverPoint

end LeanFormal.IUT.XiFPaper.S2831GluedOverPointMapActual
end
