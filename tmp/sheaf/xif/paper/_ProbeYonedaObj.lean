import Mathlib
open CategoryTheory
universe u
variable {C : Type u} [Category C] (X Z : C)
#check yoneda_obj_obj
#check yoneda_obj_map
#check (yoneda.obj X).obj (Opposite.op Z)
#reduce (yoneda.obj X).obj (Opposite.op Z)