import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantRadicalBridge

/-!
# ShehddInvariantRadicalConsumerActualAdapted — ABC invariant radical bound consumer

STEP 0 prior-art (reuse only; A475 search: radical bridge assets found):
* ABCBridge/Arithmetic/ABCInvariantRadicalBridge.lean:
  abcJInvariant_den_primeFactors_double, _den_radical_double, _den_radical_le_product,
  abcInvariant_product_radical_le_twice_den, _den_radical_bounds,
  _den_logRadical_double, _den_logRadical_le_product;
  abcInvariant_natRadical_double_le_twice.

This file packages the j-invariant denominator radical/log comparison as one consumer for
the Frey/Legendre model radical bookkeeping.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddInvariantRadicalConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** radical bounds both ways between the j-invariant denominator and
the ABC product. -/
theorem invariant_den_radical_bounds_consumer {a b c : ℕ} (h : IsABCTriple a b c) :
    radical (abcJInvariant a b c).den ≤ radical (a * b * c) ∧
      radical (a * b * c) ≤ 2 * radical (abcJInvariant a b c).den :=
  IsABCTriple.abcJInvariant_den_radical_bounds h

/-- **PROVED consumer:** prime factors of twice the j-invariant denominator are exactly
the prime factors of the ABC product. -/
theorem invariant_den_primeFactors_consumer {a b c : ℕ} (h : IsABCTriple a b c) :
    (2 * (abcJInvariant a b c).den).primeFactors = (a * b * c).primeFactors :=
  IsABCTriple.abcJInvariant_den_primeFactors_double h

/-- **PROVED consumer:** log-radical equality (twice denominator = product) and the
one-sided log-radical inequality. -/
theorem invariant_den_logRadical_consumer {a b c : ℕ} (h : IsABCTriple a b c) :
    Real.log (radical (2 * (abcJInvariant a b c).den) : ℝ) =
        Real.log (radical (a * b * c) : ℝ) ∧
      Real.log (radical (abcJInvariant a b c).den : ℝ) ≤
        Real.log (radical (a * b * c) : ℝ) :=
  ⟨IsABCTriple.abcJInvariant_den_logRadical_double h,
    IsABCTriple.abcJInvariant_den_logRadical_le_product h⟩

/-- **PROVED consumer:** doubling a nonzero natural at most doubles its radical. -/
theorem natRadical_double_consumer {n : ℕ} (hn : n ≠ 0) :
    natRadical (2 * n) ≤ 2 * natRadical n :=
  abcInvariant_natRadical_double_le_twice hn

/-- Row record: reused radical-bridge assets vs the consumer bundle. -/
def invariantRadicalRows : List (String × String × String) :=
  [ ("prime factors of doubled denominator = product factors", "REUSED PROVED", "abcJInvariant_den_primeFactors_double")
  , ("radical double equality + bounds", "REUSED PROVED", "abcJInvariant_den_radical_double / _den_radical_bounds / abcInvariant_product_radical_le_twice_den")
  , ("log-radical equality and inequality", "REUSED PROVED", "abcJInvariant_den_logRadical_double / _den_logRadical_le_product")
  , ("natRadical doubling bound", "REUSED PROVED", "abcInvariant_natRadical_double_le_twice")
  , ("consumer bundles", "COMPOSED PROVED", "invariant_den_radical_bounds_consumer, invariant_den_primeFactors_consumer, invariant_den_logRadical_consumer, natRadical_double_consumer") ]

theorem invariantRadicalRows_length : invariantRadicalRows.length = 5 := rfl

#check invariant_den_radical_bounds_consumer
#check invariant_den_primeFactors_consumer
#check invariant_den_logRadical_consumer
#check natRadical_double_consumer
#check invariantRadicalRows_length

end LeanFormal.IUT.XiFPaper.ShehddInvariantRadicalConsumerActualAdapted
end
