import Mathlib

/-!
# Mzk1KummerSummaryActualAdapted (adapted copy, A475 reuse) — absolute Kummer summary data (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: Kummer summary as map+section+injectivity witness; genuine lemma. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerSummaryActualAdapted

/-- Kummer summary data. -/
structure KummerSummary (S T : Type*) where
  map : S → T
  sec : T → S
  sec_map : ∀ x, sec (map x) = x

/-- Genuine lemma: summary map is injective. -/
theorem KummerSummary.map_injective {S T : Type*} (k : KummerSummary S T) :
    Function.Injective k.map := by
  intro x y h
  have hx := k.sec_map x
  rw [h] at hx
  exact hx.symm.trans (k.sec_map y)

end LeanFormal.IUT.XiFPaper.Mzk1KummerSummaryActualAdapted
