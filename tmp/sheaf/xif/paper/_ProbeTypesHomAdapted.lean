import Mathlib
open CategoryTheory
universe u
#check (fun x : ULift.{u} Unit => x : ULift.{u} Unit ⟶ ULift.{u} Unit)
#check (Type u)
#check CategoryTheory.types
#print CategoryTheory.types
example (X Y : Type u) : (X ⟶ Y) = (X → Y) := rfl