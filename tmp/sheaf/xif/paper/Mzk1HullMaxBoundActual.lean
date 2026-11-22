import Mathlib

/-!
# Mzk1HullMaxBoundActual — max/min bound chains for hull volumes (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Two-sided bounds via max/min: both bounds imply max/min bounds (genuine order proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullMaxBoundActual

/-- Genuine theorem: max of two terms is bounded by a common upper bound. -/
theorem max_le_chain {a b c : ℚ} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c :=
  max_le ha hb

/-- Genuine theorem: a common lower bound bounds the min. -/
theorem le_min_chain {a b c : ℚ} (ha : c ≤ a) (hb : c ≤ b) : c ≤ min a b :=
  le_min ha hb

/-- Genuine theorem: max is monotone in both arguments. -/
theorem max_mono_chain {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d) :
    max a c ≤ max b d :=
  max_le_max hab hcd

/-- Genuine theorem: min is monotone in both arguments. -/
theorem min_mono_chain {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d) :
    min a c ≤ min b d :=
  min_le_min hab hcd

end LeanFormal.IUT.XiFPaper.Mzk1HullMaxBoundActual
