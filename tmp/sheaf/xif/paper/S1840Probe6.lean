import tmp.sheaf.xif.paper.S1824YonedaCoherenceActual

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

variable {F : Type} [Field F]
variable {S : Iut.SchemeOverField F}
variable (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)

example (P : Opposite.unop a.as ⟶ S) : Discrete.ext (Category.comp_id P) = (rfl : Discrete.mk P = Discrete.mk P) := rfl

example (P : Opposite.unop a.as ⟶ S) (eta : Pseudofunctor.StrongTrans (Y S) (Y S)) :
    eqToHom (congrArg (fun Q : Discrete (Opposite.unop a.as ⟶ S) =>
        (eta.app a).toFunctor.obj Q) (Discrete.ext (Category.comp_id P))).symm = 𝟙 ((eta.app a).toFunctor.obj (Discrete.mk P)) := rfl
