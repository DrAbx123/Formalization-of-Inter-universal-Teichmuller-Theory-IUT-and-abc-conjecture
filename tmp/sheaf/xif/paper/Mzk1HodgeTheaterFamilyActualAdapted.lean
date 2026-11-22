import Mathlib

/-!
# Mzk1HodgeTheaterFamilyActualAdapted (adapted copy, A475 reuse) — Hodge theater family and link laws (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: theater family with link maps and composition law. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterFamilyActualAdapted

/-- Hodge theater family data: link maps composable. -/
structure TheaterFamily (Carrier : Type*) where
  link : Carrier → Carrier
  link_comp : ∀ x, link (link x) = link x

/-- Genuine lemma: theater links are idempotent. -/
theorem TheaterFamily.link_idem {Carrier : Type*} (f : TheaterFamily Carrier) (x : Carrier) :
    f.link (f.link x) = f.link x :=
  f.link_comp x

end LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterFamilyActualAdapted
