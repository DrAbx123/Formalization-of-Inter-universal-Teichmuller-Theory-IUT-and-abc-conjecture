import tmp.sheaf.xif.paper.S1824YonedaCoherenceActual

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

variable {F : Type} [Field F]
variable {S : Iut.SchemeOverField F}
variable (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)

example (P : Opposite.unop a.as ⟶ S) : P ≫ 𝟙 S = P := rfl
example (P : Opposite.unop a.as ⟶ S) : (((Y S).map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj (Discrete.mk (𝟙 S))) = (Discrete.mk P) := rfl
