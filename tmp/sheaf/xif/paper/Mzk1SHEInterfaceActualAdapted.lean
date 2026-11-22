import Mathlib

/-!
# Mzk1SHEInterfaceActualAdapted (adapted copy, A475 reuse) — SHE (source hull extension) interface (genuine definitions + lemma)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal model: a source carrier with a hull predicate and an extension map that preserves the hull;
the extension of a source remains in the hull (genuine lemma from the field). Registers interface only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1SHEInterfaceActualAdapted

/-- SHE data: carrier, hull set, extension map, hull-preservation. -/
structure SHEData (Carrier : Type*) where
  hull : Set Carrier
  extend : Carrier → Carrier
  hull_preserved : ∀ x, x ∈ hull → extend x ∈ hull

/-- Genuine lemma: SHE extension preserves hull membership. -/
theorem SHEData.extend_mem_hull {Carrier : Type*} (d : SHEData Carrier)
    {x : Carrier} (hx : x ∈ d.hull) : d.extend x ∈ d.hull :=
  d.hull_preserved x hx

end LeanFormal.IUT.XiFPaper.Mzk1SHEInterfaceActualAdapted
