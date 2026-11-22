import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Category

noncomputable section
open CategoryTheory
universe v u

namespace LeanFormal.IUT.XiFPaper.S2473ActionGroupoidFiberActual

variable {C : Type u} [Category.{v} C]
variable (σ : C ⥤ C) (sq : σ ⋙ σ ≅ 𝟭 C)

/-- The two-branch hom of the action groupoid: untwisted x -> y, or twisted x -> σ y. -/
abbrev S2473Hom (x y : C) : Type v := (x ⟶ y) ⊕ (x ⟶ σ.obj y)

/-- Identity in the action groupoid, untwisted branch. -/
def S2473Id (x : C) : S2473Hom σ x x := Sum.inl (𝟙 x)

/-- Composition in the action groupoid, using σ on morphisms and the square iso. -/
def S2473Comp {x y z : C} :
    S2473Hom σ x y → S2473Hom σ y z → S2473Hom σ x z
  | Sum.inl f, Sum.inl g => Sum.inl (f ≫ g)
  | Sum.inl f, Sum.inr g => Sum.inr (f ≫ g)
  | Sum.inr f, Sum.inl g => Sum.inr (f ≫ σ.map g)
  | Sum.inr f, Sum.inr g => Sum.inl (f ≫ σ.map g ≫ sq.hom.app z)

#check S2473Hom
#check S2473Id
#check S2473Comp

end LeanFormal.IUT.XiFPaper.S2473ActionGroupoidFiberActual
end
