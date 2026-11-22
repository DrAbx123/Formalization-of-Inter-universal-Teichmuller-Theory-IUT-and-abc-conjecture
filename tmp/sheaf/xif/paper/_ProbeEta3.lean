import Mathlib.CategoryTheory.Action
open CategoryTheory
variable {G : Type} [Group G] {X : Type} [MulAction G X]
example (g : G) (x : X) :
  (CategoryTheory.actionAsFunctor G X).map
    (show SingleObj.star G ⟶ SingleObj.star G from g) x = g • x := rfl
example (g : G) (x : X) :
  ConcreteCategory.hom ((CategoryTheory.actionAsFunctor G X).map
    (show SingleObj.star G ⟶ SingleObj.star G from g)) x = g • x := rfl
