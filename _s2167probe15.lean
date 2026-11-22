import Mathlib
open Polynomial

noncomputable section

namespace S2167Probe

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

def S2167F2 : (ZMod 29)[X] := C 19 + C 24 * X + C 4 * X ^ 2

example : S2167F2.natDegree = 2 := by
  unfold S2167F2
  compute_degree!

example : S2167F2.Monic := by
  rw [Monic, leadingCoeff, show S2167F2.natDegree = 2 from by unfold S2167F2; compute_degree!]
  unfold S2167F2
  simp [coeff_C, coeff_add, coeff_mul, coeff_X_pow]

example : ∀ x : ZMod 29, S2167F2.eval x ≠ 0 := by
  decide

example : S2167F2.roots = 0 := by
  rw [Polynomial.roots_eq_zero_iff_isRoot_eq_bot (by unfold S2167F2; compute_degree!)]
  ext x
  simp only [S2167F2, eval_add, eval_C, eval_mul, eval_X, eval_pow, Pi.bot_apply, not_false_eq_true, IsRoot.def]
  decide

example : Irreducible S2167F2 := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by unfold S2167F2; compute_degree!) (by unfold S2167F2; compute_degree!)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  rw [Polynomial.mem_roots (by unfold S2167F2; compute_degree!)] at hx
  exact (by decide : ∀ x : ZMod 29, S2167F2.eval x ≠ 0) x hx

end S2167Probe
