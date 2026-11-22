import Mathlib.CategoryTheory.Category.Cat

open CategoryTheory

universe u

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (W : ↑D)
    (p : W ⟶ G.toFunctor.obj (F.toFunctor.obj X)) :
    p = p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) := by
  rw [Category.comp_id]

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (W : ↑D)
    (p : W ⟶ G.toFunctor.obj (F.toFunctor.obj X)) :
    p = p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) :=
  (Category.comp_id p).symm

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (W : ↑D)
    (p : W ⟶ G.toFunctor.obj (F.toFunctor.obj X)) :
    p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) = p :=
  Category.comp_id p

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (W : ↑D)
    (p : W ⟶ G.toFunctor.obj (F.toFunctor.obj X)) :
    p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) = p := by
  simp

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (W : ↑D)
    (p : W ⟶ G.toFunctor.obj (F.toFunctor.obj X)) :
    p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) = p := by
  rw [CategoryTheory.Cat.Hom.comp_obj]
  rw [Category.comp_id]

end
