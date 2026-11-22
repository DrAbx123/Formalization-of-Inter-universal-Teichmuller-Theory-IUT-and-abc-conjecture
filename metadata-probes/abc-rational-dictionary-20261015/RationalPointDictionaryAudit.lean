import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary

/-!
# Independent audit probe for `RationalPointDictionary`

Run `abc-rational-dictionary-audit-20261015`.  This file audits the **existing, frozen** compiled
production module `LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary`.  It reads no
production source body and rebuilds nothing.  All queries are public type queries (`#check`) and
public axiom queries (`#print axioms`); no definition or proof body is printed.

The production inventory is exactly **19 declarations = 2 definitions + 17 theorems**.

One separate, clearly-labelled **audit-only** theorem is added in the dedicated namespace
`LeanFormal.IUT.RationalPointDictionaryAudit`.  It is *not* part of the 19 production
declarations and adds no mathematics beyond unfolding the two production predicates.
-/

open LeanFormal.IUT

/-! ## A. Exact actual types of the 19 production declarations -/

-- definitions (2)
#check @LeanFormal.IUT.PositivePrimitiveAdditiveTriple
#check @LeanFormal.IUT.abcRationalPoint

-- theorems (17)
#check @LeanFormal.IUT.isABCTriple_iff_positivePrimitiveAdditiveTriple
#check @LeanFormal.IUT.abcRationalPoint_eq_div
#check @LeanFormal.IUT.ratDivNatCast_num
#check @LeanFormal.IUT.ratDivNatCast_den
#check @LeanFormal.IUT.abcRationalPoint_ne_zero
#check @LeanFormal.IUT.abcRationalPoint_ne_one
#check @LeanFormal.IUT.abcRationalPoint_num
#check @LeanFormal.IUT.abcRationalPoint_den
#check @LeanFormal.IUT.abcRationalPoint_num_natAbs
#check @LeanFormal.IUT.abcRationalPoint_reduced
#check @LeanFormal.IUT.abcRationalPoint_coordinate_coprime
#check @LeanFormal.IUT.abcRationalPoint_den_sub_num
#check @LeanFormal.IUT.abcRationalPoint_coordinates_pairwise_coprime
#check @LeanFormal.IUT.abcRationalPoint_mulHeight₁
#check @LeanFormal.IUT.abcRationalPoint_logHeight₁
#check @LeanFormal.IUT.prime_dvd_abc_iff_prime_dvd_point_coordinates
#check @LeanFormal.IUT.prime_dvd_radical_abc_iff

/-! ## B. Per-name transitive axiom closure for the 19 production declarations -/

#print axioms LeanFormal.IUT.PositivePrimitiveAdditiveTriple
#print axioms LeanFormal.IUT.abcRationalPoint
#print axioms LeanFormal.IUT.isABCTriple_iff_positivePrimitiveAdditiveTriple
#print axioms LeanFormal.IUT.abcRationalPoint_eq_div
#print axioms LeanFormal.IUT.ratDivNatCast_num
#print axioms LeanFormal.IUT.ratDivNatCast_den
#print axioms LeanFormal.IUT.abcRationalPoint_ne_zero
#print axioms LeanFormal.IUT.abcRationalPoint_ne_one
#print axioms LeanFormal.IUT.abcRationalPoint_num
#print axioms LeanFormal.IUT.abcRationalPoint_den
#print axioms LeanFormal.IUT.abcRationalPoint_num_natAbs
#print axioms LeanFormal.IUT.abcRationalPoint_reduced
#print axioms LeanFormal.IUT.abcRationalPoint_coordinate_coprime
#print axioms LeanFormal.IUT.abcRationalPoint_den_sub_num
#print axioms LeanFormal.IUT.abcRationalPoint_coordinates_pairwise_coprime
#print axioms LeanFormal.IUT.abcRationalPoint_mulHeight₁
#print axioms LeanFormal.IUT.abcRationalPoint_logHeight₁
#print axioms LeanFormal.IUT.prime_dvd_abc_iff_prime_dvd_point_coordinates
#print axioms LeanFormal.IUT.prime_dvd_radical_abc_iff

/-! ## C. AUDIT-ONLY literal predicate equivalence (SEPARATE from the 19)

Target: for all `a b c : Nat`, `IsABCTriple a b c <-> (0 < a /\ 0 < b /\ a + b = c /\
Nat.Coprime a b)`, derived from the production
`isABCTriple_iff_positivePrimitiveAdditiveTriple` together with the actual definition of
`PositivePrimitiveAdditiveTriple`.
-/

namespace LeanFormal.IUT.RationalPointDictionaryAudit

theorem auditOnlyIsABCTripleLiteralEquivalence (a b c : Nat) :
    LeanFormal.IUT.IsABCTriple a b c ↔
      (0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b) :=
  LeanFormal.IUT.isABCTriple_iff_positivePrimitiveAdditiveTriple a b c

end LeanFormal.IUT.RationalPointDictionaryAudit

#check @LeanFormal.IUT.RationalPointDictionaryAudit.auditOnlyIsABCTripleLiteralEquivalence
#print axioms LeanFormal.IUT.RationalPointDictionaryAudit.auditOnlyIsABCTripleLiteralEquivalence

/-! ## D. Known existing public dependencies (types and axiom closure) -/

#check @LeanFormal.IUT.IsABCTriple.coprime_left_right
#print axioms LeanFormal.IUT.IsABCTriple.coprime_left_right
#check @LeanFormal.IUT.IsABCTriple.pairwise_coprime
#print axioms LeanFormal.IUT.IsABCTriple.pairwise_coprime
#check @LeanFormal.IUT.IsABCTriple.radical_product_eq
#print axioms LeanFormal.IUT.IsABCTriple.radical_product_eq

#check @Height.mulHeight₁
#check @Height.logHeight₁
#check @Rat.mulHeight₁_eq_max
#check @Rat.logHeight₁_eq_log_max
#check @Rat.reduced
