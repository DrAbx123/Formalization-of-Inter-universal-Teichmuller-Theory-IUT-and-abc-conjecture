import Mathlib
open scoped BigOperators

#check (∑ k in Finset.range 5, (k : Nat))
#check (∑ k ∈ Finset.range 5, (k : Nat))
