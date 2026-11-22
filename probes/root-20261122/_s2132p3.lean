import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Basic
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section

noncomputable def g : (ZMod 29)[X] := C (12 : ZMod 29) + C 6 * X + X^2

#check Polynomial.irreducible_of_roots_mem
#check Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
#check Polynomial.irreducible_of_degree_le_three
#check Polynomial.exists_root_of_degree_eq_two
#check Polynomial.roots_eq_zero_iff
#check Associated.irreducible_iff
#check Irreducible.isUnit_mul_units

example : Irreducible g := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · intro x hx
    simp [g] at hx
    norm_num at hx
  · compute_degree
  · sorry

end
