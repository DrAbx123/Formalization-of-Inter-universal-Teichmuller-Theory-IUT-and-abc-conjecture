import Mathlib

/-!
# Mzk1RationalArithmeticBookkeepingActual — genuine rational arithmetic lemmas for gate bookkeeping

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
These are genuine Mathlib-backed lemmas used in the gate/estimate bookkeeping documents. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RationalArithmeticBookkeepingActual

/-- Chain: x <= y and y < z implies x < z (genuine). -/
theorem lt_of_le_of_lt_bookkeeping {x y z : ℚ} (hxy : x ≤ y) (hyz : y < z) : x < z :=
  lt_of_le_of_lt hxy hyz

/-- Chain: x < y and y <= z implies x < z (genuine). -/
theorem lt_of_lt_of_le_bookkeeping {x y z : ℚ} (hxy : x < y) (hyz : y ≤ z) : x < z :=
  lt_of_lt_of_le hxy hyz

/-- Product of two positive rationals is positive (genuine). -/
theorem mul_pos_bookkeeping {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  mul_pos ha hb

/-- Sum of two nonnegative rationals is nonnegative (genuine). -/
theorem add_nonneg_bookkeeping {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  add_nonneg ha hb

/-- A positive rational is nonnegative (genuine). -/
theorem nonneg_of_pos_bookkeeping {a : ℚ} (ha : 0 < a) : 0 ≤ a := le_of_lt ha

end LeanFormal.IUT.XiFPaper.Mzk1RationalArithmeticBookkeepingActual
