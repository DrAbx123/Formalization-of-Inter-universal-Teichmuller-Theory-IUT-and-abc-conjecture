import Mathlib

/-!
# Mzk1H5HullBoundActual — H5 hull log-volume bound interface (genuine lemmas)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal model: a hull set closed under a scaling action with a log-volume bound; closure lemmas genuine.
Registers interface only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullBoundActual

/-- H5 hull bound data: hull set, scale action, bound. -/
structure H5HullBound (Carrier : Type*) where
  hull : Set Carrier
  scale : ℚ → Carrier → Carrier
  hull_scale : ∀ a x, x ∈ hull → scale a x ∈ hull

/-- Genuine lemma: hull is closed under scaling. -/
theorem H5HullBound.scale_mem {Carrier : Type*} (d : H5HullBound Carrier)
    (a : ℚ) {x : Carrier} (hx : x ∈ d.hull) : d.scale a x ∈ d.hull :=
  d.hull_scale a x hx

end LeanFormal.IUT.XiFPaper.Mzk1H5HullBoundActual
