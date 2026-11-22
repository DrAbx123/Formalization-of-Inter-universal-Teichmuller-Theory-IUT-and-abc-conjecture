import Mathlib.CategoryTheory.Category.Cat

open CategoryTheory

section

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (W : ↑D)
    (p : W ⟶ G.toFunctor.obj (F.toFunctor.obj X)) :
    p = p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) :=
  (Category.comp_id p).symm

example {D : Cat.{0, 0}} {Y Z : ↑D} (p : Y ⟶ Y) (e : Y ≅ Z) :
    p = (p ≫ e.inv) ≫ e.hom := by
  exact (Eq.trans (Eq.trans (Category.assoc _ _ _)
    (congrArg (fun t => _ ≫ t) (CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app e Y)))
    (Category.comp_id _)).symm

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) (W : ↑D)
    (p : W ⟶ G.toFunctor.obj (F.toFunctor.obj X)) :
    p = p ≫ (𝟙 ((F ≫ G).toFunctor.obj X)) := by
  exact (Category.comp_id p).symm

-- with an iso at the level of a Cat-composite
example {B C D E : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : ↑B)
    (W : ↑E) (p : W ⟶ H.toFunctor.obj (G.toFunctor.obj (F.toFunctor.obj X)))
    (e : H.toFunctor.obj (G.toFunctor.obj (F.toFunctor.obj X)) ≅
      H.toFunctor.obj (G.toFunctor.obj (F.toFunctor.obj X))) :
    p = (p ≫ e.inv) ≫ e.hom := by
  exact (Eq.trans (Eq.trans (Category.assoc _ _ _)
    (congrArg (fun t => _ ≫ t) e.inv_hom_id))
    (Category.comp_id _)).symm

end
