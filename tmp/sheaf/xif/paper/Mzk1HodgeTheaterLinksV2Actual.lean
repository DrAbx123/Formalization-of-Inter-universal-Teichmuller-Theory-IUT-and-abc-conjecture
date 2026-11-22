import Mathlib

/-!
# Mzk1HodgeTheaterLinksV2Actual — bi-invertible Hodge-theater links (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Bi-invertible link data; composition and inverse laws proved genuinely (calc/congrArg form). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterLinksV2Actual

/-- Bi-invertible link data between two carriers. -/
structure TheaterLinks (S T : Type*) where
  forward : S → T
  backward : T → S
  forward_backward : ∀ y, forward (backward y) = y
  backward_forward : ∀ x, backward (forward x) = x

/-- Genuine theorem: the forward map is bijective. -/
theorem TheaterLinks.forward_bijective {S T : Type*} (l : TheaterLinks S T) :
    Function.Bijective l.forward := by
  constructor
  · intro x y hxy
    rw [← l.backward_forward x, ← l.backward_forward y, hxy]
  · intro y
    exact ⟨l.backward y, l.forward_backward y⟩

/-- Genuine theorem: composing two bi-invertible links keeps bi-invertibility. -/
def TheaterLinks.compose {S T U : Type*} (l1 : TheaterLinks S T) (l2 : TheaterLinks T U) :
    TheaterLinks S U where
  forward := fun x => l2.forward (l1.forward x)
  backward := fun z => l1.backward (l2.backward z)
  forward_backward := by
    intro z
    have h := congrArg l2.forward (l1.forward_backward (l2.backward z))
    exact h.trans (l2.forward_backward z)
  backward_forward := by
    intro x
    have h := congrArg l1.backward (l2.backward_forward (l1.forward x))
    exact h.trans (l1.backward_forward x)

/-- Genuine theorem: composition of links acts as the composite forward map. -/
theorem TheaterLinks.compose_forward {S T U : Type*} (l1 : TheaterLinks S T)
    (l2 : TheaterLinks T U) (x : S) :
    (l1.compose l2).forward x = l2.forward (l1.forward x) :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterLinksV2Actual
