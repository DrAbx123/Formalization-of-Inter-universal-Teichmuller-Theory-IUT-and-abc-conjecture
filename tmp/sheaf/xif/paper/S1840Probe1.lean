import tmp.sheaf.xif.paper.S1824YonedaCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

universe u

variable {F : Type u} [Field F]
variable {S : Iut.SchemeOverField F}
variable (G : Iut.EtaleStackPseudofunctor F)

-- defeq of the two 1-morphism indices
example (eta : Pseudofunctor.StrongTrans (Y S) G)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    (((Y S).map f).toFunctor.obj P).as.op.toLoc = Quiver.Hom.toLoc P.as.op ≫ f := rfl

example (eta : Pseudofunctor.StrongTrans (Y S) G)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    eta.naturality ((((Y S).map f).toFunctor.obj P).as.op.toLoc) =
      eta.naturality (Quiver.Hom.toLoc P.as.op ≫ f) := rfl

-- unitNat hom component at P
example (eta : Pseudofunctor.StrongTrans (Y S) G)
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    (unitNat G eta a).hom.toNatTrans.app P =
      eqToHom (congrArg (fun Q : Discrete (Opposite.unop a.as ⟶ S) =>
        (eta.app a).toFunctor.obj Q) (Discrete.ext (Category.comp_id P.as))).symm ≫
        (CategoryTheory.Cat.Hom.toNatIso (eta.naturality (Quiver.Hom.toLoc P.as.op))).hom.app (Discrete.mk (𝟙 S)) := by
  rw [unitNat_hom_app]

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
