import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteMeasureEmptyActual — degree-zero characterisation (real)

Real Lean (no sorry/axiom): a finite set has maximal degree zero iff it is empty; useful for
the base case of the finite nested induction.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureEmptyActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem eq_empty_of_maxDeg_eq_zero (S : Finset Qbar) (h : maxDeg S = 0) : S = ∅ := by
  by_contra hne
  have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨x, hx⟩ := hnonempty
  have hle : degQ x <= maxDeg S := by
    unfold maxDeg
    exact Finset.le_sup hx
  have hpos : 0 < degQ x := degQ_pos x
  omega

theorem maxDeg_eq_zero_iff_empty (S : Finset Qbar) :
    maxDeg S = 0 <-> S = ∅ := by
  constructor
  · exact eq_empty_of_maxDeg_eq_zero S
  · intro h
    rw [h]
    unfold maxDeg
    simp

def finiteMeasureEmptyRows : List (String × String) :=
  [ ("eq_empty_of_maxDeg_eq_zero", "PROVED"), ("maxDeg_eq_zero_iff_empty", "PROVED") ]

theorem finiteMeasureEmptyRows_length : finiteMeasureEmptyRows.length = 2 := rfl

#check maxDeg_eq_zero_iff_empty

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureEmptyActual
end
