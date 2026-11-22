import Mathlib.CategoryTheory.Action
open CategoryTheory
variable {G : Type} [Group G] {X : Type} [MulAction G X]
variable {f g : ActionCategory G X} (η : f ⟶ g)
example : (show G from η.val) • f.back = g.back := η.property
example : (show G from η.val) • f.back = g.back := by simpa using η.property
