import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

/-! # Bad-part arithmetic: log of prime-power product as weighted log sum -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BadPartArithmeticShaActual

/-- Bad-part arithmetic: the log of a finite product of positive prime powers is the
weighted sum of logs. -/
theorem log_prod_prime_powers {ι : Type*} (s : Finset ι)
    (p : ι → Nat) (e : ι → Nat)
    (hp : ∀ i, i ∈ s → 0 < p i) :
    Real.log (∏ i ∈ s, (p i : Real) ^ e i) =
      ∑ i ∈ s, (e i : Real) * Real.log (p i) := by
  have hne : ∀ i ∈ s, ((p i : Real) ^ e i) ≠ 0 := by
    intro i hi
    exact ne_of_gt (pow_pos (by exact_mod_cast hp i hi) _)
  rw [Real.log_prod hne]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Real.log_pow]

#print axioms log_prod_prime_powers

end LeanFormal.IUT.XiFPaper.Mzk1BadPartArithmeticShaActual
