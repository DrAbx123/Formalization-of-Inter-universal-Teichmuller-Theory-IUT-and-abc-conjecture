import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S2520GaloisCoreActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2521CoverMorphismsActual

universe u

structure CoverMorphisms
    {F : Type u} [Field F] (X : Iut.HyperbolicOrbicurve F)
    (coverCategory : Category.{u + 1, u + 1} (Iut.OrbicurveFiniteEtaleCover X)) where
  coverMorphism :
    letI := coverCategory
    ∀ {source target : Iut.OrbicurveFiniteEtaleCover X},
      (source ⟶ target) → source.source.Hom target.source
  coverMorphism_over :
    letI := coverCategory
    ∀ {source target : Iut.OrbicurveFiniteEtaleCover X}
      (map : source ⟶ target),
      Iso
        (Pseudofunctor.StrongTrans.vcomp
          (coverMorphism map) target.map)
        source.map
  coverMorphism_bijective :
    letI := coverCategory
    ∀ {source target : Iut.OrbicurveFiniteEtaleCover X},
      Function.Bijective
        (fun map : source ⟶ target =>
          ({ map := coverMorphism map
             commutes := coverMorphism_over map } :
            OrbicurveFiniteEtaleCoverMap source target))
  coverMorphism_id :
    letI := coverCategory
    ∀ (cover : Iut.OrbicurveFiniteEtaleCover X),
      Iso
        (coverMorphism (𝟙 cover))
        (Pseudofunctor.StrongTrans.id cover.source.fiber)
  coverMorphism_comp :
    letI := coverCategory
    ∀ {first second third : Iut.OrbicurveFiniteEtaleCover X}
      (f : first ⟶ second) (g : second ⟶ third),
      Iso
        (coverMorphism (f ≫ g))
        (Pseudofunctor.StrongTrans.vcomp
          (coverMorphism f) (coverMorphism g))

#check CoverMorphisms
end LeanFormal.IUT.XiFPaper.S2521CoverMorphismsActual
end