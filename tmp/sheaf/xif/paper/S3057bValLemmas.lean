import tmp.sheaf.xif.paper.S3050ConnectedSite
import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import tmp.sheaf.xif.paper.S1971ActionStackificationActual
import tmp.sheaf.xif.paper.S3035RestrictionSignActual
noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3050ConnectedSite
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
namespace LeanFormal.IUT.XiFPaper.S3057bValLemmas
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev K : Type := S3050ConnectedSite.K
abbrev X : Iut.SchemeOverField K := S2844D6F6BaseChangeActual.S2844X
abbrev F' : (S3050ConnectedScheme)ᵒᵖ ⥤ Cat :=
  S3050ConnectedProperty.ι.op ⋙ S2882A6PFunctor

abbrev Q : Pseudofunctor (LocallyDiscrete S3050ConnectedSchemeᵒᵖ) Cat :=
  F'.toPseudofunctor'

local instance mulActionPoint (Y : Iut.SchemeOverField K) :
    MulAction Iut.SignGroup (Y ⟶ X) :=
  S2882A6PointMulAction (LocallyDiscrete.mk (Opposite.op Y))

lemma map₂_val {a b : LocallyDiscrete S3050ConnectedSchemeᵒᵖ}
    {f g : a ⟶ b} (ψ : f ⟶ g) (M : Q.obj a) :
    ((Q.map₂ ψ).toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  have h : f = g := LocallyDiscrete.eq_of_hom ψ
  subst h
  have hψ : ψ = 𝟙 f := Subsingleton.elim _ _
  subst hψ
  rw [PrelaxFunctor.map₂_id]
  exact ActionCategory.id_val _

lemma map₂Iso_hom_val {a b : LocallyDiscrete S3050ConnectedSchemeᵒᵖ}
    {f g : a ⟶ b} (e : f ≅ g) (M : Q.obj a) :
    ((Q.map₂Iso e).hom.toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  change ((Q.map₂ e.hom).toNatTrans.app M).val = (1 : Iut.SignGroup)
  exact map₂_val e.hom M

lemma map₂Iso_inv_val {a b : LocallyDiscrete S3050ConnectedSchemeᵒᵖ}
    {f g : a ⟶ b} (e : f ≅ g) (M : Q.obj a) :
    ((Q.map₂Iso e).inv.toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  change ((Q.map₂ e.inv).toNatTrans.app M).val = (1 : Iut.SignGroup)
  exact map₂_val e.inv M

lemma mapComp_hom_val {a b c : LocallyDiscrete S3050ConnectedSchemeᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (M : Q.obj a) :
    ((Q.mapComp f g).hom.toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  rw [show Q.mapComp _ _ = F'.toPseudofunctor'.mapComp _ _ from rfl]
  rw [Functor.toPseudofunctor'_mapComp]
  rw [show (eqToIso _).hom = eqToHom _ from rfl]
  rw [CategoryTheory.Cat.eqToHom_app]
  · exact S1971ActionCategory_eqToHom_val _
  · rfl

lemma mapComp_inv_val {a b c : LocallyDiscrete S3050ConnectedSchemeᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (M : Q.obj a) :
    ((Q.mapComp f g).inv.toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  rw [show Q.mapComp _ _ = F'.toPseudofunctor'.mapComp _ _ from rfl]
  rw [Functor.toPseudofunctor'_mapComp]
  rw [show (eqToIso _).inv = eqToHom _ from rfl]
  rw [CategoryTheory.Cat.eqToHom_app]
  · exact S1971ActionCategory_eqToHom_val _
  · rfl

lemma mapComp'_hom_val {a b c : LocallyDiscrete S3050ConnectedSchemeᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg) (M : Q.obj a) :
    ((Q.mapComp' f g fg h).hom.toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  have h1 : ((Q.mapComp f g).hom.toNatTrans.app M).val = (1 : Iut.SignGroup) :=
    mapComp_hom_val f g M
  rw [Pseudofunctor.mapComp']
  rw [Iso.trans_hom]
  rw [CategoryTheory.Cat.Hom₂.comp_app]
  rw [ActionCategory.comp_val]
  rw [h1]
  simp [map₂_val]
  exact one_mul (1 : Iut.SignGroup)

lemma mapComp'_inv_val {a b c : LocallyDiscrete S3050ConnectedSchemeᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg) (M : Q.obj a) :
    ((Q.mapComp' f g fg h).inv.toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  have h1 : ((Q.mapComp f g).inv.toNatTrans.app M).val = (1 : Iut.SignGroup) :=
    mapComp_inv_val f g M
  rw [Pseudofunctor.mapComp']
  rw [Iso.trans_inv]
  rw [CategoryTheory.Cat.Hom₂.comp_app]
  rw [ActionCategory.comp_val]
  rw [h1]
  simp [map₂_val]
  exact one_mul (1 : Iut.SignGroup)

lemma map_obj_back {Y Z : S3050ConnectedScheme} (f : Y ⟶ Z)
    (p : Q.obj (LocallyDiscrete.mk (Opposite.op Z))) :
    ((Q.map f.op.toLoc).toFunctor.obj p).back = f.hom ≫ p.back := by
  rfl

lemma map_map_val {Y Z : S3050ConnectedScheme} (f : Y ⟶ Z)
    {p q : Q.obj (LocallyDiscrete.mk (Opposite.op Z))} (φ : p ⟶ q) :
    ((Q.map f.op.toLoc).toFunctor.map φ).val = φ.val := by
  rfl

lemma pullHom_val {Y Y' X1 X2 : S3050ConnectedScheme}
    {f1 : Y ⟶ X1} {f2 : Y ⟶ X2}
    {M1 : Q.obj (LocallyDiscrete.mk (Opposite.op X1))}
    {M2 : Q.obj (LocallyDiscrete.mk (Opposite.op X2))}
    (φ : (Q.map f1.op.toLoc).toFunctor.obj M1 ⟶ (Q.map f2.op.toLoc).toFunctor.obj M2)
    (g : Y' ⟶ Y) (gf1 : Y' ⟶ X1) (gf2 : Y' ⟶ X2)
    (hgf1 : g ≫ f1 = gf1) (hgf2 : g ≫ f2 = gf2) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf1 gf2 hgf1 hgf2).val = φ.val := by
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [ActionCategory.comp_val]
  rw [ActionCategory.comp_val]
  rw [mapComp'_inv_val]
  rw [map_map_val]
  rw [mapComp'_hom_val]
  change (1 : Iut.SignGroup) * φ.val * 1 = φ.val
  rw [one_mul, mul_one]

#check mapComp'_hom_val
#check pullHom_val
#print axioms pullHom_val


lemma presheafHom_map_val
    {S : S3050ConnectedScheme}
    (M N : Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    {T₁ T₂ : Over S} (p : T₂ ⟶ T₁)
    (x : (Q.presheafHom M N).obj (Opposite.op T₁)) :
    ((Q.presheafHom M N).map p.op x).val = x.val := by
  change (Pseudofunctor.LocallyDiscreteOpToCat.pullHom x
    p.left T₂.hom T₂.hom p.w p.w).val = x.val
  exact pullHom_val x p.left T₂.hom T₂.hom p.w p.w

#check presheafHom_map_val
#print axioms presheafHom_map_val

end LeanFormal.IUT.XiFPaper.S3057bValLemmas