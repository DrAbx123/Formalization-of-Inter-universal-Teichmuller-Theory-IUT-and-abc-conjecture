import tmp.sheaf.xif.paper.S1802BicategoricalYonedaActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

variable {F : Type} [Field F]
variable {S : Iut.SchemeOverField F}
variable (G : Iut.EtaleStackPseudofunctor F)

example (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (P : Discrete (Opposite.unop a.as ⟶ S)) :
    ((Y S).map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj (Discrete.mk (𝟙 S)) =
      Discrete.mk (P.as ≫ 𝟙 S) := rfl

example (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (P : Discrete (Opposite.unop a.as ⟶ S)) :
    (((Y S).map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj (Discrete.mk (𝟙 S))) =
      Discrete.mk (P.as ≫ 𝟙 S) := rfl
