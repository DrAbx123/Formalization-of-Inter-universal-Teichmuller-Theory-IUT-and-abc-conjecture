import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Category.Cat
open CategoryTheory
namespace TestDiscrete

example {C : Type} [Category C] {α : Type} (F G : C ⥤ Cat.of (Discrete α))
    (h : ∀ X, F.obj X = G.obj X) : F = G :=
  CategoryTheory.Functor.ext h (by
    intro X Y f
    apply ULift.ext
    exact Subsingleton.elim _ _)

example {C : Type} [Category C] {α : Type} (F G : C ⥤ Cat.of (Discrete α))
    (h : ∀ X, F.obj X = G.obj X) : F = G := by
  apply CategoryTheory.Functor.ext h
  intro X Y f
  apply ULift.ext
  exact Subsingleton.elim _ _

end TestDiscrete
