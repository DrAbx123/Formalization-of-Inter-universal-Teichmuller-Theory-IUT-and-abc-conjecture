import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import Iut.Foundations.Orbicurve
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation

namespace TestGeom
universe u

variable (F : Type u) [Field F]

noncomputable def curveScheme (W : WeierstrassCurve F) : Iut.SchemeOverField F :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F W.toAffine.CoordinateRing)))

#check curveScheme

end TestGeom
end
