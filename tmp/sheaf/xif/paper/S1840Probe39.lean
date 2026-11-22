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

example (eta : Pseudofunctor.StrongTrans (Y S) G)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b) :
    True := by
  let a' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop a.as))
  let b' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop b.as))
  let f' : a' ⟶ b' := f
  let P : Discrete (Opposite.unop a'.as ⟶ S) := Discrete.mk (by sorry)
  let Q0 : (Y S).obj a' := ((Y S).map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj (Discrete.mk (𝟙 S))
  let Xb : (G.obj b') := ((Y S).map f' ≫ eta.app b').toFunctor.obj Q0
  let Xa : (G.obj b') := (eta.app a' ≫ G.map f').toFunctor.obj Q0
  let Xc : (G.obj b') := (G.map (Quiver.Hom.toLoc P.as.op) ≫ G.map f').toFunctor.obj ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S)))
  have hnorm :
      𝟙 Xb ≫ 𝟙 Xb ≫ (eta.naturality f').hom.toNatTrans.app Q0 ≫ 𝟙 Xa ≫
        (G.map f').toFunctor.map ((eta.naturality (Quiver.Hom.toLoc P.as.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S))) ≫ 𝟙 Xc =
      (eta.naturality f').hom.toNatTrans.app (Discrete.mk P.as) ≫
        (G.map f').toFunctor.map ((eta.naturality (Quiver.Hom.toLoc P.as.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S))) := by
    dsimp only [Xb, Xa, Xc, Q0]
    simp only [Category.id_comp, Category.comp_id, CategoryTheory.Functor.comp_obj]
    rfl
  trivial

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
