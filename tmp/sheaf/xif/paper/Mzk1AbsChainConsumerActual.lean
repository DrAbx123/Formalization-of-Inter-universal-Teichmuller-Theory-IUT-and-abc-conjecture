import Mathlib

/-!
# Mzk1AbsChainConsumerActual — chained absolute-value consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumer: two-sided bounds imply absolute-value bound. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsChainConsumerActual

/-- Chained: -y ≤ x and x ≤ y implies |x| ≤ y. -/
theorem abs_le_chain {x y : ℚ} (h1 : -y ≤ x) (h2 : x ≤ y) : |x| ≤ y :=
  abs_le.mpr ⟨h1, h2⟩

/-- Chained: absolute value commutes with negation in differences. -/
theorem abs_sub_comm_chain (x y : ℚ) : |x - y| = |y - x| :=
  abs_sub_comm x y

/-- Chained: square of absolute value equals square. -/
theorem sq_abs_chain (x : ℚ) : |x| ^ 2 = x ^ 2 :=
  sq_abs x

end LeanFormal.IUT.XiFPaper.Mzk1AbsChainConsumerActual
