import Mathlib.CategoryTheory.Category.Basic
open CategoryTheory
#check (fun x : Nat => x+1 : Nat ⟶ Nat)
#check (fun x : Nat => x+1 : Nat → Nat)
example : (fun x : Nat => x+1 : Nat ⟶ Nat) = fun x => x+1 := rfl
