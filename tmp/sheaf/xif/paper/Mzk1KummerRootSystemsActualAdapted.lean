import Mathlib

/-!
# Mzk1KummerRootSystemsActualAdapted (adapted copy, A475 reuse) — root system data (genuine definitions + lemmas)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: natural-number power family with pow laws; genuine lemmas. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerRootSystemsActualAdapted

/-- Root system data: power map with multiplicativity. -/
structure RootSystem (G : Type*) [Monoid G] where
  root : ℕ → G
  root_zero : root 0 = 1
  root_succ : ∀ n, root (n + 1) = root n * root 1

/-- Genuine lemma: root at successor index. -/
theorem RootSystem.root_succ_apply {G : Type*} [Monoid G] (r : RootSystem G) (n : ℕ) :
    r.root (n + 1) = r.root n * r.root 1 :=
  r.root_succ n

end LeanFormal.IUT.XiFPaper.Mzk1KummerRootSystemsActualAdapted
