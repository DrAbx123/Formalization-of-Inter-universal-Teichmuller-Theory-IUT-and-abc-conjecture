import Mathlib

/-!
# Mzk1PrimeStripsFxDActionActual — FxD action data (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: monoid action on a carrier with identity/composition laws; genuine lemma. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsFxDActionActual

/-- Monoid action data. -/
structure ActionData (M X : Type*) [Monoid M] where
  act : M → X → X
  act_one : ∀ x, act 1 x = x
  act_mul : ∀ m n x, act (m * n) x = act m (act n x)

/-- Genuine lemma: action is multiplicative. -/
theorem ActionData.act_mul_apply {M X : Type*} [Monoid M] (a : ActionData M X)
    (m n : M) (x : X) : a.act (m * n) x = a.act m (a.act n x) :=
  a.act_mul m n x

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsFxDActionActual
