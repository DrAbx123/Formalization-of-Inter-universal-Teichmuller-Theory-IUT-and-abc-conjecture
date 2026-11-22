import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-!
# ShehddABCAdditiveFormConsumerActualAdapted — additive height-weight form consumer

STEP 0 prior-art (reuse only):
* ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean:
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2,
  ABCHeightWeightAdditiveBoundV2.exists_constant,
  ABCHeightWeightAdditiveBoundV2_of_uniform_valuation_bound;
* ABCBridge/Bridge/IUTToABC.lean: abcConjecture_iff_abcLogConjecture,
  abcConjecture_iff_abcArithmeticWeightHeightBound.

This file exposes the additive form as a consumer: the constant-extraction API, the
(documented vacuous) uniform-valuation route, and the composed ABCConjecture direction.
No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddABCAdditiveFormConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** from the additive form, extract the per-epsilon constant and
pointwise height bound. -/
theorem abcAdditive_exists_constant (h : ABCHeightWeightAdditiveBoundV2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ A : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  ABCHeightWeightAdditiveBoundV2.exists_constant h hepsilon

/-- **PROVED consumer:** the (retained, now vacuous) uniform-valuation route still
yields the additive form, hence ABC via the proved equivalence. -/
theorem abcConjecture_of_uniform_valuation_bound
    (h : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ a b c : Nat, IsABCTriple a b c →
        ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
          max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ 1 + epsilon) :
    ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr
    (ABCHeightWeightAdditiveBoundV2_of_uniform_valuation_bound h)

/-- **PROVED consumer:** ABC is equivalent to the additive height-weight form, in the
consumer direction both ways. -/
theorem abcConjecture_iff_additive_consumer :
    ABCConjecture ↔ ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2

/-- Row record: reused equivalences/API vs composed consumers. -/
def abcAdditiveRows : List (String × String × String) :=
  [ ("ABC <=> additive form", "REUSED PROVED", "ABCHeightArithmeticWeightComparison.abcConjecture_iff_ABCHeightWeightAdditiveBoundV2")
  , ("additive constant extraction API", "REUSED PROVED", "ABCHeightWeightAdditiveBoundV2.exists_constant")
  , ("uniform-valuation route", "REUSED PROVED (documented vacuous)", "ABCHeightWeightAdditiveBoundV2_of_uniform_valuation_bound")
  , ("uniform-valuation => ABC", "COMPOSED PROVED", "abcConjecture_of_uniform_valuation_bound")
  , ("uniform-valuation hypothesis itself", "REFUTED ROUTE (documented)", "original uniform bound refuted; implication retained as vacuous") ]

theorem abcAdditiveRows_length : abcAdditiveRows.length = 5 := rfl

#check abcAdditive_exists_constant
#check abcConjecture_of_uniform_valuation_bound
#check abcConjecture_iff_additive_consumer
#check abcAdditiveRows_length

end LeanFormal.IUT.XiFPaper.ShehddABCAdditiveFormConsumerActualAdapted
end
