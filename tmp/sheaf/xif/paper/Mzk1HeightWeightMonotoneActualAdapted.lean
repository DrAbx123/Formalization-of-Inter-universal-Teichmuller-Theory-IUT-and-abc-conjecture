import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: monotone uniform-valuation height comparison (real proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HeightWeightMonotoneActualAdapted

open LeanFormal.IUT

theorem height_le_mul_arithmeticWeight_of_le_bound {a b c : ℕ}
    (h : IsABCTriple a b c) {B1 B2 : ℝ} (hB : B1 ≤ B2)
    (hval : ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
      max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ B1) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      B2 * arithmeticWeight (abcRationalPoint a c) := by
  have h1 := abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound h hval
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg _
  exact le_trans h1 (mul_le_mul_of_nonneg_right hB hw)

end LeanFormal.IUT.XiFPaper.Mzk1HeightWeightMonotoneActualAdapted