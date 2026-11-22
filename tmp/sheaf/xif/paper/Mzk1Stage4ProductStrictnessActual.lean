import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4ProductStrictnessActual (stage4 lane; unique filename)

A578 module: stage4-lane product strictness — a factorwise-nondecreasing product of
positive reals with one strict factor is strictly smaller.  This is the product-side
input to strict_measure for product-ball regions.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessActual

/-- Two-factor product strictness: if `0 ≤ a ≤ c`, `0 ≤ b ≤ d` and one factor is
strict, then the product is strict. -/
theorem mul_lt_mul_of_le_of_lt {a b c d : Real}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (hac : a ≤ c) (hbd : b ≤ d)
    (hstrict : a < c ∨ b < d) : a * b < c * d := by
  have h1 : a * b ≤ c * b := mul_le_mul_of_nonneg_right hac (le_of_lt hb)
  have h2 : c * b ≤ c * d := mul_le_mul_of_nonneg_left hbd (le_of_lt hc)
  rcases hstrict with h | h
  · have hlt : a * b < c * b := mul_lt_mul_of_pos_right h hb
    linarith
  · have hlt : c * b < c * d := mul_lt_mul_of_pos_left h hc
    linarith

/-- Single-factor product strictness: increasing one factor of a nonnegative product
strictly increases the product. -/
theorem mul_left_strict {a b c : Real} (hb : 0 < b) (h : a < c) :
    a * b < c * b :=
  mul_lt_mul_of_pos_right h hb

/-- Product strictness in the two-factor `r * r'` form for positive data. -/
theorem mul_strict_both_pos {a b c d : Real} (ha : 0 < a) (hb : 0 < b)
    (hac : a < c) (hbd : b < d) : a * b < c * d := by
  have hc : 0 < c := lt_trans ha hac
  have h1 : a * b < c * b := mul_lt_mul_of_pos_right hac hb
  have h2 : c * b < c * d := mul_lt_mul_of_pos_left hbd hc
  linarith

#check mul_lt_mul_of_le_of_lt
#check mul_left_strict
#check mul_strict_both_pos

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessActual
end
