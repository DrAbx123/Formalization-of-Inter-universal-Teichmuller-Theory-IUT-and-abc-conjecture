import LeanFormal.IUT.Foundations.Arithmetic.Radical

/-!
# ShehddRadicalLawsConsumerActualAdapted — natRadical arithmetic consumer

STEP 0 prior-art (reuse only; A475 search: radical laws found):
* Foundations/Arithmetic/Radical.lean: natRadical_zero, natRadical_pos,
  natRadical_dvd_self, natRadical_eq_one_iff, natRadical_eq_prod_primeFactors,
  natRadical_pow, natRadical_dvd_radical_of_dvd, natRadical_mul_of_coprime,
  natRadical_mul_three_of_pairwise_coprime, coprime_add_left/right.

This file packages the natRadical arithmetic as one consumer for the ABC radical
bookkeeping.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddRadicalLawsConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** basic natRadical laws (zero, positivity, divides self,
triviality criterion). -/
theorem natRadical_basic_consumer {n : Nat} :
    natRadical 0 = 1 ∧ 0 < natRadical n ∧ natRadical n ∣ n ∧
      (natRadical n = 1 ↔ n ≤ 1) :=
  ⟨natRadical_zero, natRadical_pos n, natRadical_dvd_self,
    natRadical_eq_one_iff⟩

/-- **PROVED consumer:** multiplicativity on coprime factors and on three pairwise
coprime factors. -/
theorem natRadical_mul_consumer {a b c : Nat}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    natRadical (a * b) = natRadical a * natRadical b ∧
      natRadical (a * b * c) =
        natRadical a * natRadical b * natRadical c :=
  ⟨natRadical_mul_of_coprime hab,
    natRadical_mul_three_of_pairwise_coprime hab hac hbc⟩

/-- **PROVED consumer:** radical of a positive power and monotonicity under divisibility. -/
theorem natRadical_pow_dvd_consumer {n k a b : Nat} (hk : k ≠ 0) (h : a ∣ b) :
    natRadical (n ^ k) = natRadical n ∧ natRadical a ∣ natRadical b :=
  ⟨natRadical_pow hk, natRadical_dvd_radical_of_dvd h⟩

/-- Row record: reused radical laws vs the consumer bundles. -/
def radicalLawsRows : List (String × String × String) :=
  [ ("valuation-style basics (zero/pos/dvd/one-iff)", "REUSED PROVED", "natRadical_zero / _pos / _dvd_self / _eq_one_iff")
  , ("prime-factor product formula", "REUSED PROVED", "natRadical_eq_prod_primeFactors")
  , ("multiplicativity (2 and 3 pairwise coprime)", "REUSED PROVED", "natRadical_mul_of_coprime / _mul_three_of_pairwise_coprime")
  , ("power and divisibility monotonicity", "REUSED PROVED", "natRadical_pow / _dvd_radical_of_dvd")
  , ("consumer bundles", "COMPOSED PROVED", "natRadical_basic_consumer, natRadical_mul_consumer, natRadical_pow_dvd_consumer") ]

theorem radicalLawsRows_length : radicalLawsRows.length = 5 := rfl

#check natRadical_basic_consumer
#check natRadical_mul_consumer
#check natRadical_pow_dvd_consumer
#check radicalLawsRows_length

end LeanFormal.IUT.XiFPaper.ShehddRadicalLawsConsumerActualAdapted
end
