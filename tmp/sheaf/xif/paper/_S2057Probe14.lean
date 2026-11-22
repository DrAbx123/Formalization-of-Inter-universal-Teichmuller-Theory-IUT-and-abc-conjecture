import Mathlib.Algebra.Group.TypeTags.Basic
#check Multiplicative.ofAdd_nsmul
#check @Multiplicative.ofAdd_nsmul
example (a : Real) (n : Nat) : Multiplicative.ofAdd a ^ n = Multiplicative.ofAdd (n • a) := by
  simp
