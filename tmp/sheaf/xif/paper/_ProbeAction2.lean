import Mathlib.CategoryTheory.Action
open CategoryTheory
variable (G : Type) [Group G] (X : Type) [MulAction G X]
#check (actionAsFunctor G X).map
#check ((actionAsFunctor G X).map (1:G))
#check (actionAsFunctor G X).map (1:G) 
