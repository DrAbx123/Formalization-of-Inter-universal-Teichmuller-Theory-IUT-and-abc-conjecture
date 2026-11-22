import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteMeasureImageActual — image bound for the finite measure (real)

Real Lean (no sorry/axiom): the maximal degree of an image is bounded by any pointwise bound
on the function.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_image_le (S : Finset Qbar) (f : Qbar -> Qbar) (M : Nat)
    (h : forall x, x ∈ S -> degQ (f x) <= M) :
    maxDeg (S.image f) <= M := by
  unfold maxDeg
  apply Finset.sup_le
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact h x hx

def finiteMeasureImageRows : List (String × String) :=
  [ ("maxDeg_image_le", "PROVED") ]

theorem finiteMeasureImageRows_length : finiteMeasureImageRows.length = 1 := rfl

#check maxDeg_image_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageActual
end
