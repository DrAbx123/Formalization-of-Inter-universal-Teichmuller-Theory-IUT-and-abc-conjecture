import Mathlib

/-!
# Hayashi extension-quantifier diagnostic

This file records a logical countermodel to the quantifier inference
"for every M there is a base with at least M witnesses" =>
"there is one base with infinitely many witnesses".
It is not an arithmetic counterexample to Hayashi's Extension Lemma or to IUT.

The residue statement below is likewise only a countermodel to an automatic
factorization inference: exact integer-valued data need not be determined by
any one fixed finite residue. It asserts nothing about a particular arithmetic
quantity in Hayashi's setting.
-/

namespace LeanFormal.HayashiExtensionQuantifiers

/-- Candidate base has the finite witness set {0, ..., base - 1}. -/
def candidateWitnesses (base : Nat) : Finset Nat := Finset.range base

theorem candidateWitnesses_card (base : Nat) :
    (candidateWitnesses base).card = base := by
  simp [candidateWitnesses]

/-- The family has witnesses of arbitrarily large finite cardinality. -/
theorem arbitrarily_many_witnesses :
    ∀ M : Nat, ∃ base : Nat,
      M ≤ base ∧ M ≤ (candidateWitnesses base).card := by
  intro M
  exact ⟨M, le_rfl, by simp [candidateWitnesses]⟩

theorem each_candidate_witnesses_finite (base : Nat) :
    (candidateWitnesses base : Set Nat).Finite := by
  exact Finset.finite_toSet (candidateWitnesses base)

theorem no_fixed_candidate_has_infinitely_many_witnesses (base : Nat) :
    ¬ (candidateWitnesses base : Set Nat).Infinite := by
  intro hinfinite
  exact hinfinite (each_candidate_witnesses_finite base)

/-- The finite-family model refutes the proposed quantifier implication. -/
theorem unbounded_finite_family_does_not_imply_infinite_member :
    ¬ ((∀ M : Nat, ∃ base : Nat,
        M ≤ base ∧ M ≤ (candidateWitnesses base).card) →
      ∃ base : Nat, (candidateWitnesses base : Set Nat).Infinite) := by
  intro h
  rcases h arbitrarily_many_witnesses with ⟨base, hinfinite⟩
  exact no_fixed_candidate_has_infinitely_many_witnesses base hinfinite

/-- A quantity factors through modulus m if it depends only on n % m. -/
def factorsThroughFiniteResidue (Q : Nat → Nat) (m : Nat) : Prop :=
  ∃ g : Nat → Nat, ∀ n : Nat, Q n = g (n % m)

/-- Exact integer data given by the identity cannot factor through a positive
    fixed finite modulus. The residues of 0 and m agree, but their values do
    not. -/
theorem identity_does_not_factor_through_positive_modulus (m : Nat)
    (hm : 0 < m) :
    ¬ factorsThroughFiniteResidue (fun n : Nat => n) m := by
  rintro ⟨g, hg⟩
  have hzero := hg 0
  have hmodulus := hg m
  simp at hzero hmodulus
  omega

/-- In particular, finite precision p^K does not determine this exact value.
    No primality assumption is needed; p >= 2 merely makes the intended
    prime-power interpretation explicit. -/
theorem identity_does_not_factor_through_prime_power (p K : Nat)
    (hp : 2 ≤ p) :
    ¬ factorsThroughFiniteResidue (fun n : Nat => n) (p ^ K) := by
  apply identity_does_not_factor_through_positive_modulus (p ^ K)
  exact pow_pos (by omega) K

end LeanFormal.HayashiExtensionQuantifiers
