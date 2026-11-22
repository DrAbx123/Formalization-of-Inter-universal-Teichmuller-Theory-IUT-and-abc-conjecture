import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4ProductStrictnessConsumerActual (stage4 lane; unique filename)

A583 module: continuation of the product strictness lemmas in mixed ≤/< factor forms
(pure real algebra).  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessConsumerActual

/-- Mixed form: `a ≤ c`, `b < d`, positive data ⇒ strictly smaller product. -/
theorem mul_lt_mul_of_le_of_lt' {a b c d : Real}
    (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbd : b < d) :
    a * b < c * d := by
  have h1 : a * b ≤ c * b := mul_le_mul_of_nonneg_right hac (le_of_lt hb)
  have h2 : c * b < c * d := mul_lt_mul_of_pos_left hbd (lt_of_lt_of_le ha hac)
  linarith

/-- Mixed form: `a < c`, `b ≤ d`, positive data ⇒ strictly smaller product. -/
theorem mul_lt_mul_of_lt_of_le' {a b c d : Real}
    (ha : 0 < a) (hb : 0 < b) (hac : a < c) (hbd : b ≤ d) :
    a * b < c * d := by
  have h1 : a * b < c * b := mul_lt_mul_of_pos_right hac hb
  have h2 : c * b ≤ c * d := mul_le_mul_of_nonneg_left hbd (le_of_lt (lt_trans ha hac))
  linarith

/-- Both-strict form (re-exported helper with positive data). -/
theorem mul_lt_mul_of_lt_of_lt' {a b c d : Real}
    (ha : 0 < a) (hb : 0 < b) (hac : a < c) (hbd : b < d) :
    a * b < c * d :=
  mul_lt_mul_of_le_of_lt' ha hb (le_of_lt hac) hbd

/-- Product monotonicity: nonnegative factors preserve ≤. -/
theorem mul_le_mul_of_nonneg' {a b c d : Real}
    (hac : a ≤ c) (hbd : b ≤ d) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b ≤ c * d :=
  mul_le_mul hac hbd hb hc

#check mul_lt_mul_of_le_of_lt'
#check mul_lt_mul_of_lt_of_le'
#check mul_lt_mul_of_lt_of_lt'
#check mul_le_mul_of_nonneg'

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessConsumerActual
end
