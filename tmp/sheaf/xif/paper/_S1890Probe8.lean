import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Functor.Category
open CategoryTheory

namespace T9
universe u
variable {C : Type u} [Category.{u,u} C]
variable {a b c d e : C}

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) :
    (f ≫ g) ≫ h ≫ k = f ≫ g ≫ h ≫ k := by
  simp only [Category.assoc]

example (A : a ⟶ b) (B : b ⟶ c) (x : c ⟶ d) (y : d ⟶ e) (z : e ⟶ e) (D : e ⟶ e) :
    A ≫ B ≫ (x ≫ y ≫ z) ≫ D = A ≫ B ≫ x ≫ y ≫ z ≫ D := by
  simp only [Category.assoc]

end T9

namespace T10
universe u v w
variable {C₀ : Type u} [Category.{u,u} C₀] {C₁ : Type v} [Category.{v,v} C₁]
  {C₂ : Type w} [Category.{w,w} C₂]
variable (c₂ : C₁ ⥤ C₂) (α₁ : C₀ ⟶ C₁) (c₁ : C₀ ⟶ C₁) (β₁ : C₀ ⟶ C₁)
  (h : C₀ ⟶ C₀)

example : c₂.map (α₁ ≫ c₁ ≫ β₁) = c₂.map α₁ ≫ c₂.map c₁ ≫ c₂.map β₁ := by
  simp only [Functor.map_comp]

end T10
