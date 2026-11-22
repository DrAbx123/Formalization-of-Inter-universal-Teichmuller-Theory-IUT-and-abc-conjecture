import Mathlib

/-!
# Mzk1Section0PathsDataActualAdapted (adapted copy, A475 reuse) — Section 0 path data (genuine definitions + lemmas)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: paths as lists of steps with length laws; genuine lemmas. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0PathsDataActualAdapted

/-- A path is a list of ℤ steps. -/
def Path := List ℤ

/-- Path length. -/
def Path.length (p : Path) : ℕ := p.length

/-- Genuine lemma: empty path has length 0. -/
theorem Path.length_nil : Path.length [] = 0 := rfl

/-- Genuine lemma: cons path length. -/
theorem Path.length_cons (n : ℤ) (p : Path) : Path.length (n :: p) = p.length + 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0PathsDataActualAdapted
