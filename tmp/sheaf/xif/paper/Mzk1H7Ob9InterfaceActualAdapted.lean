import Mathlib

/-!
# Mzk1H7Ob9InterfaceActualAdapted (adapted copy, A475 reuse) — H7/Ob9 two-sided bound interface (genuine definitions + lemmas)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal model: two-sided rational bounds (upper/lower) on a value; transitivity/monotonicity lemmas genuine.
Registers interface only (paper theorem not proved). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H7Ob9InterfaceActualAdapted

/-- Two-sided bound: lower ≤ x ≤ upper. -/
def TwoSidedBound (upper lower x : ℚ) : Prop := lower ≤ x ∧ x ≤ upper

/-- Genuine lemma: transitivity of two-sided bounds. -/
theorem TwoSidedBound.trans {u l x y : ℚ} (hx : TwoSidedBound u l x) (hxy : x ≤ y)
    (hy : y ≤ u) : TwoSidedBound u l y :=
  ⟨le_trans hx.1 hxy, hy⟩

/-- Genuine lemma: bounds are monotone in the value. -/
theorem TwoSidedBound.mono {u l x y : ℚ} (h : TwoSidedBound u l x) (hxy : x ≤ y)
    (hyu : y ≤ u) : l ≤ y ∧ y ≤ u :=
  ⟨le_trans h.1 hxy, hyu⟩

end LeanFormal.IUT.XiFPaper.Mzk1H7Ob9InterfaceActualAdapted
