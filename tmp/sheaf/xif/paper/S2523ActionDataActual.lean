import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S2522FiberDataActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2523ActionDataActual

universe u

structure ActionData
    {F : Type u} [Field F] (X : Iut.HyperbolicOrbicurve F)
    (coverCategory : Category.{u + 1, u + 1} (Iut.OrbicurveFiniteEtaleCover X))
    (galoisCategory :
      letI := coverCategory
      @GaloisCategory (Iut.OrbicurveFiniteEtaleCover X) coverCategory)
    (fiber :
      letI := coverCategory
      Iut.OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u})
    (fiberFunctor :
      letI := coverCategory
      letI := galoisCategory
      PreGaloisCategory.FiberFunctor fiber)
    (group : ProfiniteGrp.{u}) where
  action :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      MulAction group (fiber.obj cover)
  isFundamentalGroup :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    letI (cover : Iut.OrbicurveFiniteEtaleCover X) := action cover
    PreGaloisCategory.IsFundamentalGroup fiber group

#check ActionData
end LeanFormal.IUT.XiFPaper.S2523ActionDataActual
end