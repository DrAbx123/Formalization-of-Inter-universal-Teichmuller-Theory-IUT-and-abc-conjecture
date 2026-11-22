import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
open CategoryTheory

namespace T3
universe u

abbrev IC {A B C : Type u} [Category.{u,u} A] [Category.{u,u} B] [Category.{u,u} C]
    (L : A ⥤ C) (R : B ⥤ C) : Type u :=
  ObjectProperty.FullSubcategory (fun X : Comma L R => IsIso X.hom)

variable {A : Type u} [Category.{u,u} A] {L R : A ⥤ A} (F G : IC L R ⥤ IC L R)

example (e : ∀ X, F.obj X ≅ G.obj X) : F ≅ G :=
  NatIso.ofComponents (fun X => e X) (fun {X Y} f => by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact (e X).hom.hom.left
    · exact (e X).hom.hom.right)

example (X : IC L R) (l : X.obj.left ≅ X.obj.left) (r : X.obj.right ≅ X.obj.right)
    (h : L.map l.hom ≫ X.obj.hom = X.obj.hom ≫ R.map r.hom) :
    X.obj ≅ X.obj :=
  Comma.isoMk l r h

end T3
