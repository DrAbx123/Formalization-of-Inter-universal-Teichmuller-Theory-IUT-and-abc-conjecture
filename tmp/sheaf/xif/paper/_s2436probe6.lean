import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.ZMod.Basic

open CategoryTheory
open scoped Bicategory

set_option autoImplicit false

namespace Probe2436

abbrev X : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ
abbrev S : AddCommGrpCat.{0} := AddCommGrpCat.of ℚ
abbrev T : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod 2)

noncomputable def f : X ⟶ S := AddCommGrpCat.ofHom (Int.castAddHom ℚ)
noncomputable def m : X ⟶ T := AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))

instance : Mono f := by
  constructor
  intro Z g₁ g₂ h
  rw [← AddCommGrpCat.ofHom_hom g₁, ← AddCommGrpCat.ofHom_hom g₂]
  congr 1
  apply AddMonoidHom.ext
  intro x
  have hx := congrFun (congrArg (fun (k : Z ⟶ S) => (k : Z → ℚ)) h) x
  simp only [ConcreteCategory.comp_apply] at hx
  exact Int.cast_injective hx

noncomputable def yonedaCat : (AddCommGrpCat.{0})ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (Discrete (U.unop ⟶ T))
  map {U V} g := (Discrete.functor (fun h : U.unop ⟶ T => Discrete.mk (g.unop ≫ h))).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    rfl
  map_comp {U V W} f g := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    simp [Category.assoc]

noncomputable def F : Pseudofunctor (LocallyDiscrete (AddCommGrpCat.{0})ᵒᵖ) Cat.{0,0} :=
  yonedaCat.toPseudofunctor'

noncomputable def D : F.DescentData (fun _ : Unit => f) where
  obj _ := Discrete.mk m
  hom := by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    have h : f₁ = f₂ := (cancel_mono f).mp (by rw [hf₁, hf₂])
    subst h
    exact 𝟙 _
  pullHom_hom := by
    intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    haveI : Subsingleton ((F.map gf₁.op.toLoc).toFunctor.obj (Discrete.mk m) ⟶
        (F.map gf₂.op.toLoc).toFunctor.obj (Discrete.mk m)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _
  hom_self := by
    intro Y q i g hg
    obtain rfl : i = () := Subsingleton.elim i ()
    haveI : Subsingleton ((F.map g.op.toLoc).toFunctor.obj (Discrete.mk m) ⟶
        (F.map g.op.toLoc).toFunctor.obj (Discrete.mk m)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    obtain rfl : i₃ = () := Subsingleton.elim i₃ ()
    haveI : Subsingleton ((F.map f₁.op.toLoc).toFunctor.obj (Discrete.mk m) ⟶
        (F.map f₃.op.toLoc).toFunctor.obj (Discrete.mk m)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _

end Probe2436
