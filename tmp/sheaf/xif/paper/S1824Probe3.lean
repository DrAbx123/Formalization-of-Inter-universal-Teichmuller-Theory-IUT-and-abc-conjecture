import tmp.sheaf.xif.paper.S1802BicategoricalYonedaActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

universe u

variable {F : Type u} [Field F]
variable {S : Iut.SchemeOverField F}
variable (G : Iut.EtaleStackPseudofunctor F)

example (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (Y S).mapId a =
      CategoryTheory.Functor.toPseudofunctor'.mapId (Iut.schemeRepresentableFiberFunctor F S) a := rfl

example (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    ((Y S).mapId a).hom = eqToHom (by
      simp only [Y, Iut.schemeRepresentableEtalePseudofunctor, Iut.schemeRepresentableFiberFunctor,
        CategoryTheory.Functor.toPseudofunctor'_mapId]) := by
  simp only [Y, Iut.schemeRepresentableEtalePseudofunctor, Iut.schemeRepresentableFiberFunctor,
    CategoryTheory.Functor.toPseudofunctor'_mapId]

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
