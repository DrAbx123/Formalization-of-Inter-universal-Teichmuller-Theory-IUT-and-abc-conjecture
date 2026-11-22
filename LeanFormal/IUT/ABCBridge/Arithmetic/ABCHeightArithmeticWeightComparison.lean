/-
  Conditional comparison of the canonical height of the actual ABC rational point
  `x = a / c` with the restricted arithmetic weight of `x` (IUT → ABC height line H1).

  The two objects compared here are the ones already produced by the accepted dictionary:

  * `Height.logHeight₁ (abcRationalPoint a c)` — the actual Mathlib canonical height of the
    rational point `x = a / c` of an `IsABCTriple a b c` (`RationalPointDictionary`), expanded
    over the accepted `arithmeticPrimeSupport x` in
    `abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport`
    (`ABCInvariantLocalHeight.lean:136`) as

      `∑ p ∈ arithmeticPrimeSupport x, max 0 (−v_p(x)) · log p`;

  * `arithmeticWeight x = ∑ p ∈ arithmeticPrimeSupport x, log p`
    (`RationalPrimeSupport.lean:34`), the *unweighted* sum of `log p` over the same support.

  The comparison of the weighted sum with the unweighted sum is **not** proved
  unconditionally, and it cannot be: the weight `max 0 (−v_p(a/c)) = v_p(c)` at a prime
  `p ∣ c` is unbounded over the triples.  Explicit counterexamples to any uniform
  `logHeight₁ ≤ arithmeticWeight` (and even to `logHeight₁ ≤ (1+ε)·arithmeticWeight` for a
  single fixed `ε` with no additive constant) follow directly from the proved identities:

  * `(a, b, c) = (1, 8, 9)`: `x = 1/9`, `Height.logHeight₁ x = log 9`, while
    `arithmeticWeight x = log (rad 72) = log 6`; here `log 9 > log 6`;
  * `(a, b, c) = (3, 2, 5)`: `x = 3/5`, `Height.logHeight₁ x = log 5`,
    `arithmeticWeight x = log 30`.

  Consequently the statements below prove only the *conditional* comparison: they assume, as an
  explicit hypothesis, a uniform bound on the local valuation weights
  `max 0 (−v_p(x)) ≤ B` (respectively `≤ 1 + ε`) for every prime `p` in the arithmetic
  support, and conclude the height bound from it by a term-by-term comparison of the two sums.
  This reduces the whole H1 gap to that explicit `v_p` uniform-bound hypothesis; it does not
  remove it.

  No conductor is involved anywhere in this file: the arithmetic prime support is an
  *arithmetic* support of the rational point, not an elliptic-curve conductor, and no minimal
  model, reduction type or conductor exponent is referenced.

  Axiom footprint: each public declaration below depends only on the standard three axioms
  `propext`, `Classical.choice`, `Quot.sound`.
-/
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalHeight
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT

/-- **Conditional height/weight comparison with a general uniform valuation constant.**

If every local valuation weight of the actual ABC point `x = a / c` over its
`arithmeticPrimeSupport` is bounded by a fixed real `B`, then the canonical height of `x` is
bounded by `B` times its arithmetic weight.  The proof is a term-by-term comparison of

`∑ p ∈ support, max 0 (−v_p(x)) · log p` and `B · ∑ p ∈ support, log p`

using the expansion `abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport`; each factor
`Real.log p` is nonnegative because `p` is a prime of the support.

This is the general-constant form of the H1 conditional reduction: no positivity hypothesis on
`B` is needed, because `max 0 (−v_p(x)) ≤ B` already forces `max 0 (−v_p(x)) · log p ≤ B · log p`
for the nonnegative factor `log p`. -/
theorem abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound
    {a b c : ℕ} (h : IsABCTriple a b c) {B : ℝ}
    (hbound : ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
      max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ B) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      B * arithmeticWeight (abcRationalPoint a c) := by
  rw [abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport h]
  unfold arithmeticWeight
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hprime : p.Prime := by
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  exact mul_le_mul_of_nonneg_right (hbound p hp) hlog

/-- **Conditional height/weight comparison in the `(1 + ε)`-normalized H1 shape.**

If every local valuation weight of the actual ABC point `x = a / c` over its
`arithmeticPrimeSupport` is bounded by `1 + ε`, then

`Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + ε) · arithmeticWeight (abcRationalPoint a c)`.

This is the exact conditional shape recorded for gap H1: the uniform `v_p` bound
`max 0 (−v_p(x)) ≤ 1 + ε` for all `p` in the support is the only unproved input.

The hypothesis `h_eps : 0 ≤ eps` is kept for fidelity to the frozen H1 statement (it fixes the
intended regime `eps ≥ 0`), but it is not consumed by the proof: the comparison is valid for
every real `eps` as soon as the valuation bound holds.  The general-constant version
`abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound` is the
form that makes this independence explicit. -/
theorem abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound
    {a b c : ℕ} (h : IsABCTriple a b c) {eps : ℝ} (h_eps : 0 ≤ eps)
    (hbound : ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
      max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ 1 + eps) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
  abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound h hbound

/-- **Consumer-shaped version with an explicit additive constant `D`.**

For a uniform valuation bound `max 0 (−v_p(x)) ≤ 1 + eps` holding for the whole family of ABC
triples, the height bound holds in the additive-constant shape used by the Corollary 3.12 → ABC
consumer (`Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight`,
`Cor312ToABCBridgeInterface.lean:204`, and the final bound of
`abcConjecture_iff_abcArithmeticWeightHeightBound`, `IUTToABC.lean:57`):

`∀ a b c, IsABCTriple a b c → logHeight₁ x ≤ (1 + eps)·arithmeticWeight x + D`,

with `D` independent of the triple.  Any `D ≥ 0` is admissible; in fact `D = 0` already
suffices, because the pointwise theorem
`abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound` produces the
bound with no additive term.  The statement is recorded in this shape only to expose that the
H1 conditional reduction lands directly in the consumer's form and that no additional additive
error is introduced by the comparison step. -/
theorem abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_add_of_uniform_valuation_bound
    {eps D : ℝ} (h_eps : 0 ≤ eps) (hD : 0 ≤ D)
    (hbound : ∀ a b c : ℕ, IsABCTriple a b c →
      ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ 1 + eps) :
    ∀ a b c : ℕ, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D := by
  intro a b c habc
  exact le_trans
    (abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound
      habc h_eps (hbound a b c habc))
    (le_add_of_nonneg_right hD)
/-! ## Version-2 interface (contract v2, re-freeze 2026-10-16)

The uniform valuation bound of §1.1–§1.3 above is refuted: the probe
`H1UniformValuationBoundCounterexampleProbe.lean` proves
`no_oneAdd_valuation_bound` — for every real `ε` the shape
`∀ p ∈ support, max 0 (−v_p) ≤ 1 + ε` is unsatisfiable (witness family
`(1, 2^k − 1, 2^k)`, `k > 1 + ε`).  The versioned contract below replaces it as
the consumer-facing shape by the **global additive form** of IUT IV Theorem A
(`ht_{ωX(D)} ≲ (1 + ε)(log-diff + log-cond)`, bounded discrepancy classes,
corpus IV:93–105), which is already proved equivalent to `ABCConjecture` in this
repository (`abcConjecture_iff_abcArithmeticWeightHeightBound`, `IUTToABC.lean`).
All declarations above are retained unchanged; they remain true conditionals with
a premise that is now known to be refuted, and nothing is deleted or re-stated. -/

/-- **Version-2 contract (global additive form).**  For every `ε > 0` there is a
constant `A` depending only on `ε` with
`logHeight₁ (abcRationalPoint a c) ≤ (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A`
on all ABC triples.  This is literally the right-hand side of
`abcConjecture_iff_abcArithmeticWeightHeightBound` (`IUTToABC.lean`); by that
proved equivalence the contract is equivalent to `ABCConjecture`, and it is not
touched by the witness family (a family refutation of it would refute
`ABCConjecture`). -/
def ABCHeightWeightAdditiveBoundV2 : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A

/-- The version-2 contract is exactly the height form whose equivalence with
`ABCConjecture` is already proved (`IUTToABC.lean`, SHA 5F0DC873…); the statement
is definitional unfolding of the contract. -/
theorem abcConjecture_iff_ABCHeightWeightAdditiveBoundV2 :
    ABCConjecture ↔ ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_abcArithmeticWeightHeightBound

/-- Consumer API of the version-2 contract: at a fixed `ε > 0`, extract the
additive constant and the per-triple bound. -/
theorem ABCHeightWeightAdditiveBoundV2.exists_constant
    (h : ABCHeightWeightAdditiveBoundV2) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  h epsilon hepsilon

/-- The refuted uniform-bound route still implies the version-2 contract (the
implication is vacuous now; it is kept to document the relationship between the
retained §1.1–§1.3 shapes and contract v2). -/
theorem ABCHeightWeightAdditiveBoundV2_of_uniform_valuation_bound
    (h : ∀ epsilon : Real, 0 < epsilon →
      ∀ a b c : Nat, IsABCTriple a b c →
        ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
          max 0 (-(padicValRat p (abcRationalPoint a c) : Real)) ≤ 1 + epsilon) :
    ABCHeightWeightAdditiveBoundV2 :=
  fun epsilon hepsilon =>
    ⟨0, fun a b c habc =>
      by simpa using
        abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound
          habc hepsilon.le (h epsilon hepsilon a b c habc)⟩

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def abcHeightArithmeticWeightComparison : Obligation :=
  { id := "ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison"
    source := "IUT to ABC height line H1; conditional height/weight comparison"
    status := VerificationStatus.conditional
    note :=
      "From a uniform valuation bound `max 0 (-v_q) <= 1 + eps` on the prime " ++
        "support of the actual ABC rational point, the restricted arithmetic " ++
        "weight comparison is proved for every ABC triple; the unconditional " ++
        "comparison is not proved and is refuted by explicit examples. Consumed " ++
        "by `IUT-III.cor312-comparison-gap-reduction`. Name-level registration; " ++
        "no new mathematics." }

end LeanFormal.IUT.Audit
