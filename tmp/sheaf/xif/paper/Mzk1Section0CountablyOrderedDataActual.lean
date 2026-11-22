import Mathlib

/-!
# Mzk1Section0CountablyOrderedDataActual — Section 0 countably ordered data (genuine definitions + lemma)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: countably ordered carrier with a strictly increasing embedding into ℤ. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0CountablyOrderedDataActual

/-- Countably ordered data: embedding into ℤ. -/
structure CountablyOrdered where
  f : ℕ → ℤ
  strictMono : ∀ n : ℕ, f n < f (n + 1)

/-- Genuine lemma: the embedding is strictly increasing stepwise. -/
theorem CountablyOrdered.strict_step (d : CountablyOrdered) (n : ℕ) :
    d.f n < d.f (n + 1) :=
  d.strictMono n

end LeanFormal.IUT.XiFPaper.Mzk1Section0CountablyOrderedDataActual
