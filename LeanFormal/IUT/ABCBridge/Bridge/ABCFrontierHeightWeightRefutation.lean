import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierSingletonReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312PointwiseMembershipWeakening

/-!
# Refutation of the frontier sub-clause F4a and of every reduced frontier containing it

`FrontierHeightWeightClause` (F4a, `ABCFrontierReductions.lean:77`) asserts, for every
`ε > 0` and every ABC triple, `logHeight₁ (a/c) ≤ (1 + ε) · arithmeticWeight (a/c)` with
**no additive constant**.  At the triple `(1, 8, 9)` the height is `log 9` and the weight is
`log (rad 72) = log 6`; since `6^11 < 9^10`, the clause fails at `ε = 1/10`.  This is the
counterexample already recorded in prose at `ABCHeightArithmeticWeightComparison.lean:24`;
here it is proved against the frontier clause itself.

Consequence: F4a is a conjunct of `ABCFrontierGapReduced` and `ABCFrontierGapReducedV2`
(also of `ABCFrontierPointwiseWeakened`, refuted below, and of
`ABCFrontierPointwiseReduced`, already refuted by
`not_ABCFrontierPointwiseReduced`), so none of these reduced frontiers is inhabited.  The
reduction implications into `ABCFrontier` remain valid but have empty premises.  The
unreduced `ABCFrontier` is unaffected (`abcFrontier_iff_abcConjecture`); the only repair of
F4a with a slack constant is `ABCHeightWeightAdditiveBoundV2`, which is equivalent to ABC
(`abcConjecture_iff_ABCHeightWeightAdditiveBoundV2`), so a factorization through it does not
reduce the problem.
-/

namespace LeanFormal.IUT

/-- `(1, 8, 9)` is an ABC triple. -/
theorem isABCTriple_one_eight_nine : IsABCTriple 1 8 9 :=
  ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 8⟩

/-- The logarithmic height of `x = 1/9` is `log 9`. -/
theorem logHeight₁_abcRationalPoint_one_nine :
    Height.logHeight₁ (abcRationalPoint 1 9) = Real.log 9 := by
  rw [abcRationalPoint_logHeight₁ isABCTriple_one_eight_nine]
  norm_num

/-- The arithmetic weight of `x = 1/9` is `log 6 = log (rad 72)`. -/
theorem arithmeticWeight_abcRationalPoint_one_nine :
    arithmeticWeight (abcRationalPoint 1 9) = Real.log 6 := by
  rw [arithmeticWeight_abcRationalPoint isABCTriple_one_eight_nine]
  have h8 : natRadical 8 = 2 := by
    rw [natRadical_eq_prod_primeFactors, show (8 : ℕ) = 2 ^ 3 by norm_num,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
    simp
  have h9 : natRadical 9 = 3 := by
    rw [natRadical_eq_prod_primeFactors, show (9 : ℕ) = 3 ^ 2 by norm_num,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
    simp
  have h72 : natRadical (8 * 9) = natRadical 8 * natRadical 9 :=
    natRadical_mul_of_coprime (by norm_num : Nat.Coprime 8 9)
  rw [show 1 * 8 * 9 = 8 * 9 by norm_num, h72, h8, h9]
  norm_num

/-- At `(1, 8, 9)` the height exceeds `(1 + 1/10)` times the weight. -/
theorem oneAdd_tenth_mul_arithmeticWeight_lt_logHeight₁_one_eight_nine :
    (1 + 1 / 10 : ℝ) * arithmeticWeight (abcRationalPoint 1 9) <
      Height.logHeight₁ (abcRationalPoint 1 9) := by
  rw [logHeight₁_abcRationalPoint_one_nine, arithmeticWeight_abcRationalPoint_one_nine]
  have hlt : Real.log ((6 : ℝ) ^ 11) < Real.log ((9 : ℝ) ^ 10) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlt
  push_cast at hlt
  linarith

/-- **F4a is false.**  The height/weight clause without additive constant fails at
`ε = 1/10` on the triple `(1, 8, 9)`. -/
theorem not_FrontierHeightWeightClause : ¬ FrontierHeightWeightClause := by
  intro h
  have := h (1 / 10) (by norm_num) 1 8 9 isABCTriple_one_eight_nine
  linarith [oneAdd_tenth_mul_arithmeticWeight_lt_logHeight₁_one_eight_nine]

universe u

/-- The gap-reduction frontier is uninhabited (it contains F4a). -/
theorem not_ABCFrontierGapReduced : ¬ ABCFrontierGapReduced.{u} := by
  rintro ⟨_, _, _, hhw, _⟩
  exact not_FrontierHeightWeightClause hhw

/-- The F4b-refined gap frontier is uninhabited (it contains F4a). -/
theorem not_ABCFrontierGapReducedV2 : ¬ ABCFrontierGapReducedV2.{u} := by
  rintro ⟨_, _, _, hhw, _⟩
  exact not_FrontierHeightWeightClause hhw

/-- The weakened pointwise frontier is uninhabited (it contains F4a). -/
theorem not_ABCFrontierPointwiseWeakened : ¬ ABCFrontierPointwiseWeakened.{u} := by
  rintro ⟨_, _, _, hhw, _⟩
  exact not_FrontierHeightWeightClause hhw

end LeanFormal.IUT
