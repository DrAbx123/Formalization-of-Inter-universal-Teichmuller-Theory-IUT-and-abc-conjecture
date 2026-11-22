import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open CategoryTheory

namespace S1890Probe

universe u

abbrev IsoComma {A B C : Type u} [Category.{u, u} A] [Category.{u, u} B]
    [Category.{u, u} C] (L : A ⥤ C) (R : B ⥤ C) : Type u :=
  ObjectProperty.FullSubcategory (fun X : Comma L R => IsIso X.hom)

noncomputable def IsoCommaFst {A B C : Type u} [Category.{u, u} A] [Category.{u, u} B]
    [Category.{u, u} C] (L : A ⥤ C) (R : B ⥤ C) : IsoComma L R ⥤ A :=
  ObjectProperty.ι (fun X : Comma L R => IsIso X.hom) ⋙ Comma.fst L R

noncomputable def IsoCommaSnd {A B C : Type u} [Category.{u, u} A] [Category.{u, u} B]
    [Category.{u, u} C] (L : A ⥤ C) (R : B ⥤ C) : IsoComma L R ⥤ B :=
  ObjectProperty.ι (fun X : Comma L R => IsIso X.hom) ⋙ Comma.snd L R

theorem IsoComma_hom_ext {A B C : Type u} [Category.{u, u} A] [Category.{u, u} B]
    [Category.{u, u} C] (L : A ⥤ C) (R : B ⥤ C) {X Y : IsoComma L R} (f g : X ⟶ Y)
    (h1 : (IsoCommaFst L R).map f = (IsoCommaFst L R).map g)
    (h2 : (IsoCommaSnd L R).map f = (IsoCommaSnd L R).map g) : f = g := by
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · exact h1
  · exact h2

section Restrict

variable {A B C A' B' C' : Type u}
  [Category.{u, u} A] [Category.{u, u} B] [Category.{u, u} C]
  [Category.{u, u} A'] [Category.{u, u} B'] [Category.{u, u} C']
  {L : A ⥤ C} {R : B ⥤ C} {L' : A' ⥤ C'} {R' : B' ⥤ C'}

noncomputable def IsoCommaRestrict (F₁ : A ⥤ A') (F₂ : B ⥤ B') (F : C ⥤ C')
    (α : (F₁ ⋙ L') ≅ (L ⋙ F)) (β : (R ⋙ F) ≅ (F₂ ⋙ R')) :
    IsoComma L R ⥤ IsoComma L' R' where
  obj X :=
    ⟨(Comma.map α.hom β.hom).obj X.obj, by
      haveI hX : IsIso X.obj.hom := X.2
      let e : F.obj (L.obj X.obj.left) ≅ F.obj (R.obj X.obj.right) :=
        { hom := F.map X.obj.hom
          inv := F.map (inv X.obj.hom)
          hom_inv_id := by rw [← F.map_comp, IsIso.hom_inv_id, F.map_id]
          inv_hom_id := by rw [← F.map_comp, IsIso.inv_hom_id, F.map_id] }
      rw [Comma.map_obj_hom]
      exact (Iso.trans (α.app X.obj.left)
        (Iso.trans e (β.app X.obj.right))).isIso_hom⟩
  map f := ObjectProperty.homMk ((Comma.map α.hom β.hom).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    simp

theorem IsoCommaRestrict_obj_hom (F₁ : A ⥤ A') (F₂ : B ⥤ B') (F : C ⥤ C')
    (α : (F₁ ⋙ L') ≅ (L ⋙ F)) (β : (R ⋙ F) ≅ (F₂ ⋙ R')) (X : IsoComma L R) :
    ((IsoCommaRestrict F₁ F₂ F α β).obj X).obj.hom =
      (α.app X.obj.left).hom ≫ F.map X.obj.hom ≫ (β.app X.obj.right).hom :=
  Comma.map_obj_hom α.hom β.hom X.obj

end Restrict

/-! ## 2. The mapComp comparison -/

section Comp

variable {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type u}
  [Category.{u, u} A₀] [Category.{u, u} A₁] [Category.{u, u} A₂]
  [Category.{u, u} B₀] [Category.{u, u} B₁] [Category.{u, u} B₂]
  [Category.{u, u} C₀] [Category.{u, u} C₁] [Category.{u, u} C₂]
  {a₁ : A₀ ⥤ A₁} {a₂ : A₁ ⥤ A₂} {a₁₂ : A₀ ⥤ A₂} {ca : a₁₂ ≅ a₁ ⋙ a₂}
  {b₁ : B₀ ⥤ B₁} {b₂ : B₁ ⥤ B₂} {b₁₂ : B₀ ⥤ B₂} {cb : b₁₂ ≅ b₁ ⋙ b₂}
  {c₁ : C₀ ⥤ C₁} {c₂ : C₁ ⥤ C₂} {c₁₂ : C₀ ⥤ C₂}
  {L₀ : A₀ ⥤ C₀} {R₀ : B₀ ⥤ C₀} {L₁ : A₁ ⥤ C₁} {R₁ : B₁ ⥤ C₁}
  {L₂ : A₂ ⥤ C₂} {R₂ : B₂ ⥤ C₂}
  {α₁ : a₁ ⋙ L₁ ≅ L₀ ⋙ c₁} {β₁ : R₀ ⋙ c₁ ≅ b₁ ⋙ R₁}
  {α₂ : a₂ ⋙ L₂ ≅ L₁ ⋙ c₂} {β₂ : R₁ ⋙ c₂ ≅ b₂ ⋙ R₂}
  {α₁₂ : a₁₂ ⋙ L₂ ≅ L₀ ⋙ c₁₂} {β₁₂ : R₀ ⋙ c₁₂ ≅ b₁₂ ⋙ R₂}

variable (sq : ∀ (x : A₀) (y : B₀) (h : L₀.obj x ⟶ R₀.obj y),
    L₂.map (ca.hom.app x) ≫ α₂.hom.app (a₁.obj x) ≫ c₂.map (α₁.hom.app x) ≫
      c₂.map (c₁.map h) ≫ c₂.map (β₁.hom.app y) ≫ β₂.hom.app (b₁.obj y) =
    α₁₂.hom.app x ≫ c₁₂.map h ≫ β₁₂.hom.app y ≫ R₂.map (cb.hom.app y))

/-- **The comparison isomorphism between the restriction along a composite and the
composite of the two restrictions.** -/
noncomputable def compNatIso :
    IsoCommaRestrict (L := L₀) (R := R₀) (L' := L₂) (R' := R₂) a₁₂ b₁₂ c₁₂ α₁₂ β₁₂ ≅
      IsoCommaRestrict (L := L₀) (R := R₀) (L' := L₁) (R' := R₁) a₁ b₁ c₁ α₁ β₁ ⋙
        IsoCommaRestrict (L := L₁) (R := R₁) (L' := L₂) (R' := R₂) a₂ b₂ c₂ α₂ β₂ :=
  NatIso.ofComponents
    (fun X =>
      ObjectProperty.isoMk (P := fun Z : Comma L₂ R₂ => IsIso Z.hom)
        (Comma.isoMk
          (X := ((IsoCommaRestrict a₁₂ b₁₂ c₁₂ α₁₂ β₁₂).obj X).obj)
          (Y := (((IsoCommaRestrict a₁ b₁ c₁ α₁ β₁) ⋙
            (IsoCommaRestrict a₂ b₂ c₂ α₂ β₂)).obj X).obj)
          (ca.app X.obj.left) (cb.app X.obj.right) (by
            have h := sq X.obj.left X.obj.right X.obj.hom
            simpa only [Iso.app_hom, Functor.map_comp, Category.assoc] using h))
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact ca.hom.naturality f.hom.left
      · exact cb.hom.naturality f.hom.right)

end Comp

/-! ## 3. The mapId comparison -/

section Id

variable {A₀ B₀ C₀ : Type u}
  [Category.{u, u} A₀] [Category.{u, u} B₀] [Category.{u, u} C₀]
  {a₀ : A₀ ⥤ A₀} {ca₀ : a₀ ≅ 𝟭 A₀}
  {b₀ : B₀ ⥤ B₀} {cb₀ : b₀ ≅ 𝟭 B₀}
  {c₀ : C₀ ⥤ C₀}
  {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
  {α₀ : a₀ ⋙ L ≅ L ⋙ c₀} {β₀ : R ⋙ c₀ ≅ b₀ ⋙ R}

variable (sq : ∀ (x : A₀) (y : B₀) (h : L.obj x ⟶ R.obj y),
    L.map (ca₀.hom.app x) ≫ h = (α₀.hom.app x ≫ c₀.map h ≫ β₀.hom.app y) ≫ R.map (cb₀.hom.app y))

/-- **The comparison isomorphism between the restriction along an identity and the
identity functor.** -/
noncomputable def idNatIso :
    IsoCommaRestrict (L := L) (R := R) (L' := L) (R' := R) a₀ b₀ c₀ α₀ β₀ ≅
      𝟭 (IsoComma L R) :=
  NatIso.ofComponents
    (fun X =>
      ObjectProperty.isoMk (P := fun Z : Comma L R => IsIso Z.hom)
        (Comma.isoMk
          (X := ((IsoCommaRestrict a₀ b₀ c₀ α₀ β₀).obj X).obj)
          (Y := X.obj)
          (ca₀.app X.obj.left) (cb₀.app X.obj.right) (by
            have h := sq X.obj.left X.obj.right X.obj.hom
            simpa only [Iso.app_hom, Category.assoc] using h))
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact ca₀.hom.naturality f.hom.left
      · exact cb₀.hom.naturality f.hom.right)

end Id

end S1890Probe
