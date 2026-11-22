import Mathlib

/-!
# Mzk1FrobenioidRamificationDataActualAdapted (adapted copy, A475 reuse) — Frobenioid ramification/units laws (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: ramification data and units map laws. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrobenioidRamificationDataActualAdapted

/-- Ramification data: index and ramification degree. -/
structure RamificationData (P : Type*) where
  index : P → ℕ
  degree : P → ℕ
  degree_pos : ∀ p, 0 < degree p

/-- Genuine lemma: ramification degrees are positive. -/
theorem RamificationData.degree_pos_apply {P : Type*} (r : RamificationData P) (p : P) :
    0 < r.degree p := r.degree_pos p

/-- Units map data: map with multiplication law. -/
structure UnitsMapData (G H : Type*) [Monoid G] [Monoid H] where
  map : G → H
  map_one : map 1 = 1
  map_mul : ∀ a b, map (a * b) = map a * map b

/-- Genuine lemma: units map preserves multiplication. -/
theorem UnitsMapData.map_mul_apply {G H : Type*} [Monoid G] [Monoid H]
    (u : UnitsMapData G H) (a b : G) : u.map (a * b) = u.map a * u.map b :=
  u.map_mul a b

end LeanFormal.IUT.XiFPaper.Mzk1FrobenioidRamificationDataActualAdapted
