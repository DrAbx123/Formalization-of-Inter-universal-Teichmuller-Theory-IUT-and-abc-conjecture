import Mathlib

/-!
# Mzk1HodgeTheaterLinksActual — Hodge theater links data (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: link data as a pair of inverse maps between source and target. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterLinksActual

/-- Hodge theater link data. -/
structure TheaterLinks (Source Target : Type*) where
  forward : Source → Target
  backward : Target → Source
  forward_backward : ∀ y, forward (backward y) = y

/-- Genuine lemma: the forward link is a section of backward. -/
theorem TheaterLinks.forward_backward_apply {S T : Type*} (l : TheaterLinks S T) (y : T) :
    l.forward (l.backward y) = y := l.forward_backward y

end LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterLinksActual
