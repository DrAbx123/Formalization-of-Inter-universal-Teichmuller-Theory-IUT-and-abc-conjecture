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

noncomputable def ofMapNat (x y : G.obj (site S)) (k : x ⟶ y)
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) : ofApp G x a ⟶ ofApp G y a :=
  NatTrans.toCatHom₂ (Discrete.natTrans (fun P : Discrete (Opposite.unop a.as ⟶ S) =>
    (G.map (Quiver.Hom.toLoc P.as.op)).toFunctor.map k))

lemma ofMapNat_app (x y : G.obj (site S)) (k : x ⟶ y)
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    (ofMapNat G x y k a).toNatTrans.app P =
      (G.map (Quiver.Hom.toLoc P.as.op)).toFunctor.map k := rfl

noncomputable def ofMapMod (x y : G.obj (site S)) (k : x ⟶ y) :
    Pseudofunctor.StrongTrans.Modification (ofObjFull G x) (ofObjFull G y) where
  app a := ofMapNat G x y k a
  naturality f := by
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext P
    obtain ⟨P⟩ := P
    simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
      CategoryTheory.Cat.whiskerRight_app, ofNat_hom_app, ofObjFull_naturality,
      ofMapNat_app]
    exact (CategoryTheory.Cat.Hom.toNatIso (G.mapComp (Quiver.Hom.toLoc P.op) f)).hom.naturality k

noncomputable def ofMapHom (x y : G.obj (site S)) (k : x ⟶ y) :
    ofObjFull G x ⟶ ofObjFull G y :=
  ⟨ofMapMod G x y k⟩

noncomputable def ofObjFunctor : G.obj (site S) ⥤ Pseudofunctor.StrongTrans (Y S) G where
  obj x := ofObjFull G x
  map k := ofMapHom G _ _ k
  map_id x := by
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext P
    obtain ⟨P⟩ := P
    change ((ofMapMod G x x (𝟙 x)).app a).toNatTrans.app (Discrete.mk P) =
      ((Pseudofunctor.StrongTrans.Modification.id (ofObjFull G x)).app a).toNatTrans.app (Discrete.mk P)
    simp only [ofMapMod, ofMapNat_app, Pseudofunctor.StrongTrans.Modification.id_app,
      CategoryTheory.Cat.Hom₂.id_app, ofApp_obj, ofObjFull_app, CategoryTheory.Functor.map_id]
  map_comp k l := by
    rename_i X Y Z
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext P
    obtain ⟨P⟩ := P
    change ((ofMapMod G X Z (k ≫ l)).app a).toNatTrans.app (Discrete.mk P) =
      (((ofMapMod G X Y k).vcomp (ofMapMod G Y Z l)).app a).toNatTrans.app (Discrete.mk P)
    simp only [ofMapMod, Pseudofunctor.StrongTrans.Modification.vcomp_app,
      CategoryTheory.Cat.Hom₂.comp_app, ofMapNat_app, CategoryTheory.Functor.map_comp,
      ofApp_obj, ofObjFull_app]

noncomputable def toObjFunctor : Pseudofunctor.StrongTrans (Y S) G ⥤ G.obj (site S) where
  obj eta := toObj G eta
  map m := (m.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S))
  map_id eta := by
    change ((Pseudofunctor.StrongTrans.Modification.id eta).app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)) =
      𝟙 ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S)))
    simp
  map_comp m n := by
    change (((m.as).vcomp (n.as)).app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)) =
      (m.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)) ≫ (n.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S))
    simp

noncomputable def counitIso : ofObjFunctor G ⋙ toObjFunctor G ≅ 𝟭 (G.obj (site S)) :=
  CategoryTheory.Cat.Hom.toNatIso (G.mapId (site S))

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
