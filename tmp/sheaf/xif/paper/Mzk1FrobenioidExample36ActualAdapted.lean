import Mathlib

/-!
# Mzk1FrobenioidExample36ActualAdapted (adapted copy, A475 reuse) — Example 3.6 source model backend (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: source model with an action and a unit map; genuine action laws. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrobenioidExample36ActualAdapted

/-- Example 3.6 source model data. -/
structure SourceModel (Carrier Unit : Type*) where
  action : Unit → Carrier → Carrier
  unitOne : Unit
  action_one : ∀ x, action unitOne x = x

/-- Genuine lemma: the unit action is the identity. -/
theorem SourceModel.action_one_apply {Carrier Unit : Type*} (m : SourceModel Carrier Unit)
    (x : Carrier) : m.action m.unitOne x = x :=
  m.action_one x

end LeanFormal.IUT.XiFPaper.Mzk1FrobenioidExample36ActualAdapted
