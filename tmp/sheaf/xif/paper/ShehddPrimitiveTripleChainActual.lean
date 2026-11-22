import LeanFormal.IUT.ABCBridge.Arithmetic.PrimitiveTriple
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence

/-!
# ShehddPrimitiveTripleChainActual — ABC primitive-triple radical chain

New chain consequence of the compiled primitive-triple laws: ABC triples are pairwise
coprime, their product radical is multiplicative, coincides with the sibling radical
constant, and is positive.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddPrimitiveTripleChainActual

open LeanFormal.IUT

/-- **PROVED chain:** an ABC triple is pairwise coprime and its product radical is the
product of the radicals, equal to the `natRadical` constant, and positive. -/
theorem abcTriple_radical_chain {a b c : Nat} (h : IsABCTriple a b c) :
    ABCPairwiseCoprime a b c ∧
      radical (a * b * c) = radical a * radical b * radical c ∧
        radical (a * b * c) = natRadical (a * b * c) ∧
          0 < natRadical (a * b * c) := by
  refine ⟨h.pairwise_coprime, h.radical_product_eq,
    radical_eq_natRadical (a * b * c), ?_⟩
  exact natRadical_pos (a * b * c)

/-- **PROVED chain:** the product radical as a real number is positive. -/
theorem radical_cast_pos_chain {a b c : Nat} :
    (0 : Real) < (radical (a * b * c) : Real) := by
  rw [radical_eq_natRadical]
  exact_mod_cast natRadical_pos (a * b * c)

end LeanFormal.IUT.XiFPaper.ShehddPrimitiveTripleChainActual
end
