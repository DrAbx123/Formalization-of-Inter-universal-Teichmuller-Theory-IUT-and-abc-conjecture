import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1Stage4ProductStrictnessActual

/-! # Mzk1Stage4ProductStrictnessConsumer2Actual (stage4 lane; unique filename)

A586 module: further product strictness consumers — powers and three-factor products
(pure real algebra).  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessConsumer2Actual

/-- Strict power comparison: `0 ≤ a`, `a < b` ⇒ `a^n < b^n` for `n > 0`. -/
theorem pow_lt_pow_strict {a b : Real} (ha : 0 ≤ a) (hab : a < b) {n : Nat} (hn : 0 < n) :
    a ^ n < b ^ n :=
  pow_lt_pow_left₀ hab ha (Nat.ne_of_gt hn)

/-- Three-factor product strictness: positive factors with one strict factor and
factorwise ≤ elsewhere give a strictly smaller product. -/
theorem three_factor_strict {a b c d e f : Real}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ d) (hbc : b ≤ e) (hcf : c ≤ f)
    (hstrict : a < d ∨ b < e ∨ c < f) : a * b * c < d * e * f := by
  have hd : 0 < d := lt_of_lt_of_le ha hab
  have he : 0 < e := lt_of_lt_of_le hb hbc
  have hf : 0 < f := lt_of_lt_of_le hc hcf
  have habc : a * b * c ≤ d * e * c := by
    have h1 : a * b ≤ d * b := mul_le_mul_of_nonneg_right hab (le_of_lt hb)
    have h2 : d * b ≤ d * e := mul_le_mul_of_nonneg_left hbc (le_of_lt hd)
    have h3 : a * b * c ≤ d * e * c := by
      have := mul_le_mul_of_nonneg_right (le_trans h1 h2) (le_of_lt hc)
      simpa [mul_assoc] using this
    exact h3
  have hcdef : d * e * c ≤ d * e * f :=
    mul_le_mul_of_nonneg_left hcf (by positivity : (0 : Real) ≤ d * e)
  rcases hstrict with h | h | h
  · have h1 : a * b * c < d * b * c := by
      have := mul_lt_mul_of_pos_right h hb
      have := mul_lt_mul_of_pos_right this hc
      simpa [mul_assoc] using this
    have h2 : d * b * c ≤ d * e * f := by
      have h2a : d * b ≤ d * e := mul_le_mul_of_nonneg_left hbc (le_of_lt hd)
      have h2b : d * b * c ≤ d * e * c := by
        have := mul_le_mul_of_nonneg_right h2a (le_of_lt hc)
        simpa [mul_assoc] using this
      exact le_trans h2b hcdef
    exact lt_of_lt_of_le h1 h2
  · have h1 : d * b * c < d * e * c := by
      have := mul_lt_mul_of_pos_left h hd
      have := mul_lt_mul_of_pos_right this hc
      simpa [mul_assoc] using this
    have habc' : a * b * c ≤ d * b * c := by
      have hx : a * b ≤ d * b := mul_le_mul_of_nonneg_right hab (le_of_lt hb)
      have := mul_le_mul_of_nonneg_right hx (le_of_lt hc)
      simpa [mul_assoc] using this
    exact lt_of_lt_of_le (lt_of_le_of_lt habc' h1) hcdef
  · have h1 : d * e * c < d * e * f :=
      mul_lt_mul_of_pos_left h (by positivity : (0 : Real) < d * e)
    exact lt_of_le_of_lt habc h1
/-- Product of two strict powers versus product of two strict powers. -/
theorem pow_two_product_strict {a b c d : Real} (ha : 0 < a) (hb : 0 < b)
    (hac : a < c) (hbd : b < d) : a ^ 2 * b ^ 2 < c ^ 2 * d ^ 2 := by
  have h1 : a ^ 2 < c ^ 2 := pow_lt_pow_strict (le_of_lt ha) hac (by norm_num : (0:Nat) < 2)
  have h2 : b ^ 2 < d ^ 2 := pow_lt_pow_strict (le_of_lt hb) hbd (by norm_num : (0:Nat) < 2)
  exact Mzk1Stage4ProductStrictnessActual.mul_strict_both_pos
    (by positivity : (0 : Real) < a ^ 2) (by positivity : (0 : Real) < b ^ 2) h1 h2

#check pow_lt_pow_strict
#check three_factor_strict
#check pow_two_product_strict

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessConsumer2Actual
end
