import LeanFormal.IUT.ABCBridge.Arithmetic.ABCNonemptyOddBadSupport

/-!
# ShehddBadSupportChainActual — odd bad-prime support nonemptiness/valuation chain

New chain consequences of the compiled odd bad-support laws: nonemptiness/emptyness/card
positivity are all equivalent to the nonexceptional condition, and a support member
yields an odd prime dividing the j-denominator with negative valuation.  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddBadSupportChainActual

open LeanFormal.IUT

/-- **PROVED chain:** the odd bad-prime support is nonempty / nonempty-card iff the triple
is nonexceptional, and empty iff the triple is (1,1,2). -/
theorem abcOddBadPrimeSupport_chain {a b c : Nat} (h : IsABCTriple a b c) :
    ((abcOddBadPrimeSupport a b c).Nonempty ↔ (a, b, c) ≠ (1, 1, 2)) ∧
      (abcOddBadPrimeSupport a b c = ∅ ↔ (a, b, c) = (1, 1, 2)) ∧
        (0 < (abcOddBadPrimeSupport a b c).card ↔ (a, b, c) ≠ (1, 1, 2)) :=
  ⟨h.abcOddBadPrimeSupport_nonempty_iff,
    h.abcOddBadPrimeSupport_empty_iff,
    h.abcOddBadPrimeSupport_card_pos_iff⟩

/-- **PROVED chain:** a member of the odd bad support is an odd prime dividing the
j-invariant denominator with negative p-adic valuation. -/
theorem odd_bad_prime_valuation_chain {a b c p : Nat} (h : IsABCTriple a b c)
    (hp : p ∈ abcOddBadPrimeSupport a b c) :
    p.Prime ∧ p ≠ 2 ∧ p ∣ (abcJInvariant a b c).den ∧
      padicValRat p (abcJInvariant a b c) < 0 := by
  obtain ⟨hprime, hpne, _⟩ := h.mem_abcOddBadPrimeSupport_iff.mp hp
  exact ⟨hprime, hpne, h.odd_bad_prime_mem_dvd_j_den hp,
    h.odd_bad_prime_mem_j_valuation_neg hp⟩

/-- **PROVED chain:** a nonexceptional triple has an odd prime outside the j-denominator
with negative valuation (membership dropped). -/
theorem exists_odd_prime_valuation_neg_chain {a b c : Nat} (h : IsABCTriple a b c)
    (hne : (a, b, c) ≠ (1, 1, 2)) :
    ∃ p : Nat, p.Prime ∧ p ≠ 2 ∧ p ∣ (abcJInvariant a b c).den ∧
      padicValRat p (abcJInvariant a b c) < 0 := by
  obtain ⟨p, hp, hp2, _hmem, hden, hval⟩ :=
    h.exists_odd_prime_dvd_j_den_and_valuation_neg hne
  exact ⟨p, hp, hp2, hden, hval⟩

end LeanFormal.IUT.XiFPaper.ShehddBadSupportChainActual
end
