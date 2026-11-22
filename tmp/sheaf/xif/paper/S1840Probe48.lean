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
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    True := by
  let a' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop a.as))
  let b' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop b.as))
  let f' : a' ⟶ b' := f
  let Q0 : (Y S).obj a' := ((Y S).map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj (Discrete.mk (𝟙 S))
  let Xb : (G.obj b') := ((Y S).map f' ≫ eta.app b').toFunctor.obj Q0
  let Xa : (G.obj b') := (eta.app a' ≫ G.map f').toFunctor.obj Q0
  let Xc : (G.obj b') := (G.map f').toFunctor.obj ((G.map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))))
  let natf : Xb ⟶ Xa := (eta.naturality f').hom.toNatTrans.app Q0
  let natP : (G.map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))) ⟶ (eta.app a').toFunctor.obj Q0 := (eta.naturality (Quiver.Hom.toLoc P.as.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S))
  let mp : Xa ⟶ Xc := (G.map f').toFunctor.map natP
  have hnorm :
      𝟙 Xb ≫ 𝟙 Xb ≫ natf ≫ 𝟙 Xa ≫ mp ≫ 𝟙 Xc =
      (eta.naturality f').hom.toNatTrans.app (Discrete.mk P.as) ≫ mp := by
    have h1 : 𝟙 Xb ≫ (𝟙 Xb ≫ (natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc)))) =
        𝟙 Xb ≫ (natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc))) := Category.id_comp _
    have h2 : 𝟙 Xb ≫ (natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc))) =
        natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc)) := Category.id_comp _
    have h3 : natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc)) = natf ≫ (mp ≫ 𝟙 Xc) :=
      congrArg (fun k => natf ≫ k) (Category.id_comp _)
    have h4 : natf ≫ (mp ≫ 𝟙 Xc) = natf ≫ mp :=
      congrArg (fun k => natf ≫ k) (Category.comp_id _)
    have h5 : natf ≫ mp = (eta.naturality f').hom.toNatTrans.app (Discrete.mk P.as) ≫ mp := rfl
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  trivial

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
