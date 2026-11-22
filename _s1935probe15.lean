import Mathlib.CategoryTheory.Category.Cat

open CategoryTheory

universe u

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (Y : ↑D)
    (p : (G.toFunctor.obj (F.toFunctor.obj X)) ⟶ Y) :
    p = p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) := by
  rw [Category.comp_id]

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (Y : ↑D)
    (p : (G.toFunctor.obj (F.toFunctor.obj X)) ⟶ Y) :
    p = p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) :=
  (Category.comp_id p).symm

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (Y : ↑D)
    (p : (G.toFunctor.obj (F.toFunctor.obj X)) ⟶ Y) :
    p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) = p :=
  Category.comp_id p

end
