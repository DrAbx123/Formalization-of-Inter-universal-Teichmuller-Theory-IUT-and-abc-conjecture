import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2519CoverBaseActual

universe u

/-- Universe-corrected cover base bundle: cover category at Category.{u+1,u+1}, plus base scheme and base point. -/
structure CoverBase
    {F : Type u} [Field F] (X : Iut.HyperbolicOrbicurve F) where
  coverCategory : Category.{u + 1, u + 1} (Iut.OrbicurveFiniteEtaleCover X)
  baseScheme : Iut.SchemeOverField F
  basePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F baseScheme)
      X.stack.fiber

end LeanFormal.IUT.XiFPaper.S2519CoverBaseActual
end