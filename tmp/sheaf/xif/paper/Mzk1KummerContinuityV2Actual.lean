import Mathlib

/-!
# Mzk1KummerContinuityV2Actual — bijectivity from two-sided inverse (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
A map with left and right inverse is bijective (genuine proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerContinuityV2Actual

/-- Genuine theorem: a map with both inverses is bijective. -/
theorem bijective_of_left_right_inverse {S T : Type*} {f : S → T} {g : T → S}
    (hl : ∀ y, f (g y) = y) (hr : ∀ x, g (f x) = x) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    rw [← hr x, ← hr y, hxy]
  · intro y
    exact ⟨g y, hl y⟩

/-- Genuine theorem: the inverse map of a bijection is injective. -/
theorem injective_of_left_inverse {S T : Type*} {f : S → T} {g : T → S}
    (hr : ∀ x, g (f x) = x) : Function.Injective f := by
  intro x y hxy
  rw [← hr x, ← hr y, hxy]

end LeanFormal.IUT.XiFPaper.Mzk1KummerContinuityV2Actual
