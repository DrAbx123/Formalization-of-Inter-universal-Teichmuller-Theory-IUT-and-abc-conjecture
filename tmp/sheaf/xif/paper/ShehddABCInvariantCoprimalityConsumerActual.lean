import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantCoprimality

/-!
# ShehddABCInvariantCoprimalityConsumerActual — ABC invariant coprimality consumer

STEP 0 prior-art (reuse only; A475 search: ABCCoprimality assets found):
* ABCBridge/Arithmetic/ABCInvariantCoprimality.lean: abcInvariantPolynomial /
  abcInvariantNumerator / abcInvariantDenominator / abcInvariantCancellation /
  abcJInvariant; IsABCTriple.abcInvariantPolynomial_coprime_left/right/sum/product,
  pow_coprime_product_pow, cube_coprime_denominator, Numerator_pos, Denominator_pos,
  Cancellation_eq_gcd_coefficient/dvd_256/pos/le_256.

This file packages the invariant coprimality and cancellation bounds as one consumer for
the Frey model bookkeeping (j-invariant denominator/numerator normalization).  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddABCInvariantCoprimalityConsumerActual

open LeanFormal.IUT

/-- **PROVED consumer:** all invariant coprimality facts for an ABC triple in one bundle
(polynomial coprime to a, b, c, abc, and its cube coprime to the denominator). -/
theorem abcInvariant_coprime_summary {a b c : ℕ} (h : IsABCTriple a b c) :
    0 < abcInvariantPolynomial a b ∧
      Nat.Coprime (abcInvariantPolynomial a b) a ∧
        Nat.Coprime (abcInvariantPolynomial a b) b ∧
          Nat.Coprime (abcInvariantPolynomial a b) c ∧
            Nat.Coprime (abcInvariantPolynomial a b) (a * b * c) ∧
              Nat.Coprime (abcInvariantPolynomial a b ^ 3)
                (abcInvariantDenominator a b c) :=
  ⟨h.abcInvariantPolynomial_pos,
    h.abcInvariantPolynomial_coprime_left,
    h.abcInvariantPolynomial_coprime_right,
    h.abcInvariantPolynomial_coprime_sum,
    h.abcInvariantPolynomial_coprime_product,
    h.abcInvariantPolynomial_cube_coprime_denominator⟩

/-- **PROVED consumer:** numerator/denominator positivity and the cancellation bound
(gcd with 256, divisor of 256, in (0,256]). -/
theorem abcInvariant_cancellation_summary {a b c : ℕ} (h : IsABCTriple a b c) :
    0 < abcInvariantNumerator a b ∧
      0 < abcInvariantDenominator a b c ∧
        abcInvariantCancellation a b c ∣ 256 ∧
          0 < abcInvariantCancellation a b c ∧
            abcInvariantCancellation a b c ≤ 256 :=
  ⟨h.abcInvariantNumerator_pos,
    h.abcInvariantDenominator_pos,
    h.abcInvariantCancellation_dvd_256,
    h.abcInvariantCancellation_pos,
    h.abcInvariantCancellation_le_256⟩

/-- **PROVED consumer:** the cancellation factor is the gcd of 256 with the denominator. -/
theorem abcInvariant_cancellation_eq_gcd {a b c : ℕ} (h : IsABCTriple a b c) :
    abcInvariantCancellation a b c =
      Nat.gcd 256 (abcInvariantDenominator a b c) :=
  h.abcInvariantCancellation_eq_gcd_coefficient

/-- Row record: reused coprimality assets vs the consumer bundle. -/
def abcInvariantCoprimalityRows : List (String × String × String) :=
  [ ("polynomial positivity and invariance a^2+ab+b^2 = c^2-ab", "REUSED PROVED", "IsABCTriple.abcInvariantPolynomial_pos/_add_product")
  , ("pairwise / product coprimality", "REUSED PROVED", "coprime_left/right/sum/product")
  , ("cube coprime denominator", "REUSED PROVED", "abcInvariantPolynomial_cube_coprime_denominator")
  , ("numerator/denominator positivity + cancellation bounds", "REUSED PROVED", "Numerator_pos/Denominator_pos/Cancellation_*")
  , ("consumer bundles", "COMPOSED PROVED", "abcInvariant_coprime_summary, abcInvariant_cancellation_summary, abcInvariant_cancellation_eq_gcd") ]

theorem abcInvariantCoprimalityRows_length : abcInvariantCoprimalityRows.length = 5 := rfl

#check abcInvariant_coprime_summary
#check abcInvariant_cancellation_summary
#check abcInvariant_cancellation_eq_gcd
#check abcInvariantCoprimalityRows_length

end LeanFormal.IUT.XiFPaper.ShehddABCInvariantCoprimalityConsumerActual
end
