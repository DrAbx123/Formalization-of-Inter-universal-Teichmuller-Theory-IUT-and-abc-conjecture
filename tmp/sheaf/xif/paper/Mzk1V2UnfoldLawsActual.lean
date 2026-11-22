import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: unfolding/construction laws for the additive V2 contract (real proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1V2UnfoldLawsActual

open LeanFormal.IUT

/-- Eliminate V2 at a fixed epsilon. -/
theorem v2_apply (h : ABCHeightWeightAdditiveBoundV2) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, ∀ a b c : ℕ, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  h ε hε

/-- Introduce V2 from its pointwise bound family. -/
theorem v2_of_bounds
    (h : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ a b c : ℕ, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A) :
    ABCHeightWeightAdditiveBoundV2 :=
  h

/-- Specialization at epsilon = 1. -/
theorem v2_at_one (h : ABCHeightWeightAdditiveBoundV2) :
    ∃ A : ℝ, ∀ a b c : ℕ, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * arithmeticWeight (abcRationalPoint a c) + A := by
  simpa using v2_apply (h := h) (ε := 1) zero_lt_one

end LeanFormal.IUT.XiFPaper.Mzk1V2UnfoldLawsActual