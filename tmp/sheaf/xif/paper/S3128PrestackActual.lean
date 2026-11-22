import tmp.sheaf.xif.paper.S3128QuotientSheafStrongActual
noncomputable section
open CategoryTheory
namespace LeanFormal.IUT.XiFPaper.S3128PrestackActual
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {C : Type u₁} [Category.{v₁, u₁} C]
variable {D : Type u₂} [Category.{v₂, u₂} D]
variable {E : Type u₃} [Category.{v₃, u₃} E]

noncomputable def S3128WhiskerLeftIso
    (F : C ⥤ D) {G H : D ⥤ E} (e : G ≅ H) :
    F ⋙ G ≅ F ⋙ H where
  hom := Functor.whiskerLeft F e.hom
  inv := Functor.whiskerLeft F e.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    change e.hom.app (F.obj X) ≫ e.inv.app (F.obj X) =
      𝟙 (G.obj (F.obj X))
    exact Iso.hom_inv_id_app e (F.obj X)
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    change e.inv.app (F.obj X) ≫ e.hom.app (F.obj X) =
      𝟙 (H.obj (F.obj X))
    exact Iso.inv_hom_id_app e (F.obj X)

theorem S3128WhiskerLeftIso_trans
    (F : C ⥤ D) {G H K : D ⥤ E}
    (e : G ≅ H) (f : H ≅ K) :
    S3128WhiskerLeftIso F (e ≪≫ f) =
      S3128WhiskerLeftIso F e ≪≫ S3128WhiskerLeftIso F f := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [S3128WhiskerLeftIso, Functor.whiskerLeft,
    Iso.trans_hom, NatTrans.comp_app]
  rfl

#check S3128WhiskerLeftIso
#print axioms S3128WhiskerLeftIso

end LeanFormal.IUT.XiFPaper.S3128PrestackActual