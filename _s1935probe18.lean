import Mathlib.CategoryTheory.Category.Cat

open CategoryTheory

section

example {D : Cat.{0, 0}} {W Y Z : ↑D} (p : W ⟶ Y) (e : Z ≅ Y) :
    p = (p ≫ e.inv) ≫ e.hom := by
  exact (Eq.trans (Eq.trans (Category.assoc _ _ _)
    (congrArg (fun t => _ ≫ t) e.inv_hom_id))
    (Category.comp_id _)).symm

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (W : ↑D)
    (p : W ⟶ G.toFunctor.obj (F.toFunctor.obj X)) :
    p = (p ≫ (𝟙 ((F ≫ G).toFunctor.obj X))) ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) := by
  exact (Eq.trans (Eq.trans (Category.assoc _ _ _)
    (congrArg (fun t => _ ≫ t) (Category.id_comp (𝟙 ((F ≫ G).toFunctor.obj X))).symm))
    (Category.comp_id _)).symm

end
