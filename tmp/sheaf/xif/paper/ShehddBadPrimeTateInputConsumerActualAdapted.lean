import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison

/-!
# ShehddBadPrimeTateInputConsumerActualAdapted — odd bad-prime Frey/Tate input consumer

STEP 0 prior-art (reuse only; A475 search: ABC model height comparison found):
* ABCBridge/Geometry/ABCModelHeightComparison.lean:
  freyAbcTateCandidateQ_ne_zero_of_mem_abcOddBadPrimeSupport,
  _norm_lt_one_of_mem_abcOddBadPrimeSupport, _ne_one_of_mem_abcOddBadPrimeSupport,
  rationalFreyWeierstrassCurve_j_padicValRat_neg_of_mem_abcOddBadPrimeSupport,
  rationalFreyWeierstrassCurve_j_cast_norm_gt_one_of_mem_abcOddBadPrimeSupport,
  exists_odd_bad_prime_freyAbcTateAnalyticInput;
* ABCNonemptyOddBadSupport: abcOddBadPrimeSupport membership facts.

This file packages the odd-bad-prime Tate q-series input facts as one consumer: at any
odd prime of the bad support the candidate q := j^-1 is nonzero, contracting and not one.
No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddBadPrimeTateInputConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** at an odd bad prime the Frey/Tate candidate q is nonzero. -/
theorem frey_badprime_candidate_ne_zero_consumer {a b c p : Nat}
    (h : IsABCTriple a b c) (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    freyAbcTateCandidateQ p a b c ≠ 0 :=
  freyAbcTateCandidateQ_ne_zero_of_mem_abcOddBadPrimeSupport h hp

/-- **PROVED consumer:** at an odd bad prime the candidate is strictly contracting. -/
theorem frey_badprime_candidate_norm_lt_one_consumer {a b c p : Nat}
    (h : IsABCTriple a b c) (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    ‖freyAbcTateCandidateQ p a b c‖ < 1 :=
  freyAbcTateCandidateQ_norm_lt_one_of_mem_abcOddBadPrimeSupport h hp

/-- **PROVED consumer:** at an odd bad prime the candidate is not one. -/
theorem frey_badprime_candidate_ne_one_consumer {a b c p : Nat}
    (h : IsABCTriple a b c) (hp : p ∈ abcOddBadPrimeSupport a b c) :
    letI : Fact p.Prime := ⟨(h.mem_abcOddBadPrimeSupport_iff.mp hp).1⟩
    freyAbcTateCandidateQ p a b c ≠ 1 :=
  freyAbcTateCandidateQ_ne_one_of_mem_abcOddBadPrimeSupport h hp

/-- **PROVED consumer:** every nonexceptional ABC triple has an odd bad prime at which
the packaged Frey j/Tate analytic input holds. -/
theorem exists_tate_input_consumer {a b c : Nat} (h : IsABCTriple a b c)
    (hne : (a, b, c) ≠ (1, 1, 2)) :
    ∃ p : Nat, ∃ hp : p.Prime, p ≠ 2 ∧ p ∈ abcOddBadPrimeSupport a b c := by
  obtain ⟨p, hp, hp2, hmem, _⟩ := exists_odd_bad_prime_freyAbcTateAnalyticInput h hne
  exact ⟨p, hp, hp2, hmem⟩

/-- Row record: reused bad-prime assets vs the consumer interface. -/
def badPrimeTateRows : List (String × String × String) :=
  [ ("candidate nonzero / norm<1 / ne_one at odd bad primes", "REUSED PROVED", "freyAbcTateCandidateQ_*_of_mem_abcOddBadPrimeSupport")
  , ("j negative valuation / norm > 1 at odd bad primes", "REUSED PROVED", "rationalFreyWeierstrassCurve_j_*_of_mem_abcOddBadPrimeSupport")
  , ("existence of an odd bad prime with analytic input", "REUSED PROVED", "exists_odd_bad_prime_freyAbcTateAnalyticInput (nonexceptional triples)")
  , ("consumer wrappers", "COMPOSED PROVED", "frey_badprime_candidate_*_consumer, exists_tate_input_consumer")
  , ("candidate = genuine Tate parameter (uniformization)", "NOT CLAIMED (tree docstring)", "candidate identified only with j^-1; no uniformization asserted") ]

theorem badPrimeTateRows_length : badPrimeTateRows.length = 5 := rfl

#check frey_badprime_candidate_ne_zero_consumer
#check frey_badprime_candidate_norm_lt_one_consumer
#check exists_tate_input_consumer
#check badPrimeTateRows_length

end LeanFormal.IUT.XiFPaper.ShehddBadPrimeTateInputConsumerActualAdapted
end