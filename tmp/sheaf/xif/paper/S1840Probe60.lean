import tmp.sheaf.xif.paper.S1840UnitCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1840UnitCoherenceActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual
open LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual

universe u

variable {F : Type u} [Field F]

example (S : Iut.SchemeOverField F) (G : Iut.EtaleStackPseudofunctor F)
    (h : UnitCoherence S G)
    {eta theta : Pseudofunctor.StrongTrans (Y S) G}
    (m : eta ⟶ theta) :
    m ≫ (unitIsoOf (S := S) (G := G) h theta).hom =
      (unitIsoOf (S := S) (G := G) h eta).hom ≫
        (toObjFunctor G ⋙ ofObjFunctor G).map m := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro a
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  change (m.as.app a).toNatTrans.app (Discrete.mk P) ≫
      (unitNat G theta a).hom.toNatTrans.app (Discrete.mk P) =
    (unitNat G eta a).hom.toNatTrans.app (Discrete.mk P) ≫
      (G.map (Quiver.Hom.toLoc P.op)).toFunctor.map
        ((m.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)))
  rw [unitNat_hom_app]
  rw [unitNat_hom_app]
  simp
  have hm := congrArg (fun α => α.toNatTrans.app (Discrete.mk (𝟙 S)))
    (m.as.naturality (Quiver.Hom.toLoc P.op))
  change (m.as.app a).toNatTrans.app
        (((Y S).map (Quiver.Hom.toLoc P.op)).toFunctor.obj (Discrete.mk (𝟙 S))) ≫
      (theta.naturality (Quiver.Hom.toLoc P.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S)) =
    (eta.naturality (Quiver.Hom.toLoc P.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S)) ≫
      (G.map (Quiver.Hom.toLoc P.op)).toFunctor.map
        ((m.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)))
  exact hm
