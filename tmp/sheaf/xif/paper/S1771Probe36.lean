import Mathlib.Algebra.Category.CommAlgCat.Basic
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]
variable {A B C : CommAlgCat R}
example (f : A ⟶ B) (g : B ⟶ C) (x : A) : ((f ≫ g).hom) x = g.hom (f.hom x) := by
  rw [CommAlgCat.hom_comp]
  rfl
example (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := by
  rw [CommAlgCat.hom_comp]
#check ConcreteCategory.comp_apply
#check ConcreteCategory.hom_comp
#check CategoryTheory.ConcreteCategory.comp_apply
