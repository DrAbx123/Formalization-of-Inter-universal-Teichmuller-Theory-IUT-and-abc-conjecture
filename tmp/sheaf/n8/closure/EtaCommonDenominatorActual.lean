import Mathlib
import tmp.sheaf.n8.closure.EtaLocalizationBasisManual

/-!
# Eta common denominator actual

Actual theorem: for every finite family c : n -> Q_p there is N with
||p^N * c i|| <= 1 for all i.  Equivalently, p^N * c i is integral for all i
(the integrality membership is the subtype {x // ||x|| <= 1}).

Proof: each c i has a bound ||c i|| <= p^(N_i) since p^n tends to infinity in R;
take N = sum_i N_i and use ||p^N * c i|| = p^(-N) ||c i|| <= 1.

The full-lattice open/span step remains the missing input; no arbitrary basis is
introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.deprecated false

open scoped BigOperators

namespace LeanFormal.IUT.N8Closure.EtaCommonDenominatorActual

variable {p : Nat} [Fact p.Prime]
variable {n : Type*} [Fintype n]

/-- Actual common-denominator bound for a finite family in Q_p. -/
theorem common_denominator_norm (c : n → ℚ_[p]) :
    ∃ N : ℕ, ∀ i : n, ‖(p : ℚ_[p]) ^ N * c i‖ ≤ 1 := by
  classical
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have ht := tendsto_pow_atTop_atTop_of_one_lt hp1
  have hex : ∀ i : n, ∃ N : ℕ, ‖c i‖ ≤ (p : ℝ) ^ N := by
    intro i
    exact (ht.eventually (Filter.eventually_ge_atTop (‖c i‖))).exists
  choose N_i hN_i using hex
  let N : ℕ := ∑ i, N_i i
  refine ⟨N, fun i => ?_⟩
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
  have hNiN : N_i i ≤ N :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp1
  have hpow : (p : ℝ) ^ (N_i i) ≤ (p : ℝ) ^ N :=
    pow_le_pow_right₀ (le_of_lt hp1) hNiN
  have hbound : ‖c i‖ ≤ (p : ℝ) ^ N := le_trans (hN_i i) hpow
  have hpos : (0 : ℝ) < (p : ℝ) ^ N := pow_pos hp0 N
  rw [inv_mul_le_iff₀ hpos]
  simpa using hbound

/-- Exact missing full-lattice openness/span statement: a full Z_p-lattice L is
open at 0, hence every x has a nonzero p-power multiple inside L. -/
def MissingFullLatticeOpenSpanLemma : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (L : AddSubgroup E),
    IsOpen (L : Set E) →
    ∀ x : E, ∃ N : ℕ, (p : ℚ_[p]) ^ N • x ∈ L

end LeanFormal.IUT.N8Closure.EtaCommonDenominatorActual
