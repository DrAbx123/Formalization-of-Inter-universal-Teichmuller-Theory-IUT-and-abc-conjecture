import Mathlib

/-!
# Mzk1IPLFamilyV2Actual — monotone indexed families (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Monotone families: precomposition with monotone index map stays monotone (genuine proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IPLFamilyV2Actual

/-- A monotone index family. -/
structure MonotoneFamily (Index Prime : Type*) [Preorder Index] where
  family : Index → Set Prime
  monotone : ∀ {i j : Index}, i ≤ j → family i ⊆ family j

/-- Genuine theorem: precomposition with a monotone index map stays monotone. -/
def MonotoneFamily.precomp {Index Index' Prime : Type*} [Preorder Index] [Preorder Index']
    (d : MonotoneFamily Index Prime) (g : Index' → Index) (hg : Monotone g) :
    MonotoneFamily Index' Prime where
  family := fun i => d.family (g i)
  monotone := by
    intro i j hij
    exact d.monotone (hg hij)

/-- Genuine theorem: precomposition acts pointwise. -/
theorem MonotoneFamily.precomp_apply {Index Index' Prime : Type*} [Preorder Index]
    [Preorder Index'] (d : MonotoneFamily Index Prime) (g : Index' → Index)
    (hg : Monotone g) (i : Index') :
    (d.precomp g hg).family i = d.family (g i) :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1IPLFamilyV2Actual
