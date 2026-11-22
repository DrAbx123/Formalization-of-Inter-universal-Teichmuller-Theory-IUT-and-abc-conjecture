import Mathlib
example {A : Type*} [AddMonoid A] (a : A) : Multiplicative.toAdd (Multiplicative.ofAdd a) = a := rfl
example {A : Type*} [AddMonoid A] (a : A) : Multiplicative.ofAdd (Multiplicative.toAdd a) = a := by
  cases a; rfl
#check Multiplicative.ofAdd_apply
#check Multiplicative.toAdd_apply
#check Multiplicative.ofAdd_symm_apply
#check Multiplicative.toAdd_symm_apply
