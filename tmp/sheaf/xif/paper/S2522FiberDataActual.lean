import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S2521CoverMorphismsActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2522FiberDataActual

universe u

structure FiberData
    {F : Type u} [Field F] (X : Iut.HyperbolicOrbicurve F)
    (coverCategory : Category.{u + 1, u + 1} (Iut.OrbicurveFiniteEtaleCover X))
    (galoisCategory :
      letI := coverCategory
      @GaloisCategory (Iut.OrbicurveFiniteEtaleCover X) coverCategory)
    (baseScheme : Iut.SchemeOverField F)
    (basePoint :
      Pseudofunctor.StrongTrans
        (Iut.schemeRepresentableEtalePseudofunctor F baseScheme)
        X.stack.fiber) where
  fiber :
    letI := coverCategory
    Iut.OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u}
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber
  geometricFiberFintype :
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      Fintype
        (Iut.OrbicurveFiniteEtaleCover.GeometricFiber
          baseScheme basePoint cover)
  fiberIdentification :
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      (fiber.obj cover).obj ≃
        Iut.OrbicurveFiniteEtaleCover.GeometricFiber
          baseScheme basePoint cover

#check FiberData
end LeanFormal.IUT.XiFPaper.S2522FiberDataActual
end