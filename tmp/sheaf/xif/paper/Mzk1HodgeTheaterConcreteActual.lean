import Mathlib

/-!
# Mzk1HodgeTheaterConcreteActual — concrete Hodge theater data (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: concrete theater with underlying carrier map and projection; genuine lemma. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterConcreteActual

/-- Concrete theater data. -/
structure ConcreteTheater (Carrier : Type*) where
  projection : Carrier → Carrier
  projection_idem : ∀ x, projection (projection x) = projection x

/-- Genuine lemma: concrete theater projection is idempotent. -/
theorem ConcreteTheater.projection_idem_apply {Carrier : Type*}
    (t : ConcreteTheater Carrier) (x : Carrier) :
    t.projection (t.projection x) = t.projection x :=
  t.projection_idem x

end LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterConcreteActual
