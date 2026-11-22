import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImage2ActualAdapted

/-! # Mzk1FiniteMeasureImage3ActualAdapted — degree-preserving image equality (real)

Real Lean (no sorry/axiom): a pointwise degree-preserving map preserves the finite maximal
degree of a finite set.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage3ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage2ActualAdapted

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_image_eq_of_degQ (S : Finset Qbar) (f : Qbar -> Qbar)
    (h : forall x, degQ (f x) = degQ x) :
    maxDeg (S.image f) = maxDeg S := by
  apply le_antisymm
  · exact maxDeg_image_le_of_degQ_le S f (fun x => le_of_eq (h x))
  · unfold maxDeg
    apply Finset.sup_le
    intro x hx
    have hxeq : degQ x = degQ (f x) := (h x).symm
    rw [hxeq]
    unfold maxDeg
    exact Finset.le_sup (Finset.mem_image_of_mem f hx)

def finiteMeasureImage3Rows : List (String × String) :=
  [ ("maxDeg_image_eq_of_degQ", "PROVED") ]

theorem finiteMeasureImage3Rows_length : finiteMeasureImage3Rows.length = 1 := rfl

#check maxDeg_image_eq_of_degQ

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage3ActualAdapted
end
