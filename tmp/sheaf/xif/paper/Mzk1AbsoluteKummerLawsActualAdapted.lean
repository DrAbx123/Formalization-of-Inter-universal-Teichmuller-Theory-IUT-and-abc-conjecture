import Mathlib

/-!
# Mzk1AbsoluteKummerLawsActualAdapted (adapted copy, A475 reuse) — absolute Kummer map laws (genuine definitions + lemmas)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: absolute Kummer map with a section and injectivity consequence. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerLawsActualAdapted

/-- Absolute Kummer data: map with left inverse. -/
structure AbsoluteKummer (S T : Type*) where
  map : S → T
  section_ : T → S
  left_inv : ∀ x, section_ (map x) = x

/-- Genuine lemma: the absolute Kummer map is injective. -/
theorem AbsoluteKummer.injective {S T : Type*} (k : AbsoluteKummer S T) :
    Function.Injective k.map := by
  intro x y h
  have hx := k.left_inv x
  have hy := k.left_inv y
  rw [h] at hx
  exact hx.symm.trans hy

end LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerLawsActualAdapted
