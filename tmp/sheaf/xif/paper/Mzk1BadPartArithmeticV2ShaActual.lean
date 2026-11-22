import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

/-! # Bad-part arithmetic V2 (direct) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BadPartArithmeticV2ShaActual

theorem log_prod_prime_powers {ι : Type*} (s : Finset ι)
    (p : ι → Nat) (e : ι → Nat)
    (hp : forall i, i ∈ s → 0 < p i) :
    Real.log (Finset.prod s (fun i => (p i : Real) ^ e i)) =
      Finset.sum s (fun i => (e i : Real) * Real.log (p i)) := by
  have hne : forall i, i ∈ s → ((p i : Real) ^ e i) ≠ 0 := by
    intro i hi
    exact ne_of_gt (pow_pos (by exact_mod_cast hp i hi) _)
  rw [Real.log_prod hne]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Real.log_pow]

#print axioms log_prod_prime_powers

end LeanFormal.IUT.XiFPaper.Mzk1BadPartArithmeticV2ShaActual
