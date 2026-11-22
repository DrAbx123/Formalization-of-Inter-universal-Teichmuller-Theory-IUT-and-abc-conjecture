import Mathlib.CategoryTheory.Action
open CategoryTheory
variable {G : Type} [Group G] {X : Type} [MulAction G X]
theorem test (g : G) (x : X) :
  (CategoryTheory.actionAsFunctor G X).map
    (show CategoryTheory.SingleObj.star G ⟶ CategoryTheory.SingleObj.star G from g) x = g • x := rfl
