import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S2519CoverBaseActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2520GaloisCoreActual

universe u

structure GaloisCore
    {F : Type u} [Field F] (X : Iut.HyperbolicOrbicurve F)
    (coverCategory : Category.{u + 1, u + 1} (Iut.OrbicurveFiniteEtaleCover X)) where
  galoisCategory :
    letI := coverCategory
    @GaloisCategory (Iut.OrbicurveFiniteEtaleCover X) coverCategory

#check GaloisCore
end LeanFormal.IUT.XiFPaper.S2520GaloisCoreActual
end