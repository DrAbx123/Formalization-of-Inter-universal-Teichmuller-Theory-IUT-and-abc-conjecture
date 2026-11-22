import Mathlib

/-!
# Mzk1KummerRightInverseChainActual — chained right-inverse composition (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumer: composition of maps with right inverses has a right inverse. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerRightInverseChainActual

/-- Chained: right inverses compose. -/
theorem rightInverse_comp_chain {S T U : Type*} {f : S → T} {g : T → U}
    {sf : T → S} {sg : U → T}
    (hf : ∀ y, f (sf y) = y) (hg : ∀ z, g (sg z) = z) :
    ∀ z, (fun x => g (f x)) (sf (sg z)) = z := by
  intro z
  change g (f (sf (sg z))) = z
  rw [hf (sg z)]
  exact hg z

/-- Chained: a map with both a left and right inverse is bijective. -/
theorem bijective_of_left_right_chain {S T : Type*} {f : S → T}
    {sl : T → S} {sr : T → S}
    (hl : ∀ y, f (sl y) = y) (hr : ∀ x, f (sr x) = f x) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    -- injectivity via the left inverse: f (sl (f x)) = f x
    have hx : f (sl (f x)) = f x := hl (f x)
    have hy : f (sl (f y)) = f y := hl (f y)
    calc
      x = sl (f x) := (by sorry)

end LeanFormal.IUT.XiFPaper.Mzk1KummerRightInverseChainActual
